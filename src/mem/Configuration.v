Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import Memory.

Module Configuration.
  Structure t := mk {
    clocks: Clocks.t;
    threads: Threads.t;
    memory: Memory.t;
    stack: list (Threads.t * Memory.t);
  }.

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (STACK: c.(stack) = nil)
      (THREADS:
         forall i th (THREAD: Ident.Map.find i c.(threads) = Some th),
           Thread.is_terminal th)
  .

  Inductive is_observable (c:t): Prop :=
  | is_observable_intro
      (STACK: c.(stack) = nil)
      (MEMORY: forall i, MessageSet.Empty (Ident.Fun.find i c.(memory)).(Buffer.inception))
  .

  Inductive step: forall (c1:t) (e:option Event.t) (c2:t), Prop :=
  | step_event
      i e
      c th1 th2 m1 m2 stack
      (THREADS: Threads.step th1 i e th2)
      (MEMORY: Memory.step c m1 i e m2)
      (CONSISTENT: Memory.consistent m2):
      step (mk c th1 m1 stack) None (mk c th2 m2 stack)
  | step_dream
      c th m stack:
      step (mk c th m stack) None (mk c th m ((th, m)::stack))
  | step_inception
      c th1 m1 th2 m2 stack
      event ts1 loc val
      ts2 pos i
      (WRITING: RWEvent.is_writing event = Some (loc, val))
      (UPDATE:
         forall loc valr valw ord (EVENT: event = RWEvent.update loc valr valw ord),
         exists event0 ts0 pos0 val0,
           <<IN: Memory.In m2 (Message.rw event0 ts0) pos0>> /\
           <<TS: ts0 + 1 = ts1>> /\
           <<EVENT0: RWEvent.is_writing event0 = Some (loc, val0)>>)
      (MESSAGE: Memory.In m1 (Message.rw event ts1) pos)
      (POSITION: Memory.Position.is_inception pos = false)
      (INCEPTION:
         forall i,
           MessageSet.Subset
             (Ident.Fun.find i m1).(Buffer.inception)
             (Ident.Fun.find i m2).(Buffer.inception)):
      step
        (mk c th1 m1 ((th2, m2)::stack))
        None
        (mk c
            th2
            (Ident.Fun.add i (Buffer.add_inception (Message.rw event ts2) (Ident.Fun.find i m2)) m2)
            stack)
  | step_commit
      c1 th m c2
      (MEMORY: forall i, MessageSet.Empty (Ident.Fun.find i m).(Buffer.inception))
      (CLOCKS: Clocks.le c1 c2):
      step
        (mk c1 th m nil)
        None
        (mk c2 th m nil)
  | step_syscall
      c th1 m i e th2
      (THREADS: Threads.step th1 i (Some (ThreadEvent.syscall e)) th2):
      step
        (mk c th1 m nil)
        (Some e)
        (mk c th2 m nil)
  .
End Configuration.