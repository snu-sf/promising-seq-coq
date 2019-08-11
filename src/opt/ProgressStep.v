Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import DenseOrder.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Lemma progress_program_step
      rs1 i1 s1 lc1 sc1 mem1
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot)
      (NOHALF1: Memory.no_half mem1):
  exists e th2, <<STEP: Thread.program_step e (Thread.mk lang (State.mk rs1 (i1::s1)) lc1 sc1 mem1) th2>>.
Proof.
  destruct i1.
  - destruct i.
    + esplits. econs; [|econs 1]; eauto. econs. econs.
    + esplits. econs; [|econs 1]; eauto. econs. econs.
    + hexploit progress_read_step; eauto. i. des.
      esplits. econs; [|econs 2]; eauto. econs. econs.
    + hexploit progress_write_step; eauto.
      { apply Time.incr_spec. }
      { i. rewrite PROMISES1. apply Memory.bot_nonsynch_loc. }
      i. des. esplits. econs; [|econs 3]; eauto. econs. econs.
    + hexploit progress_read_step; eauto. i. des.
      exploit Memory.no_half_max_ts; eauto; i.
      exploit Local.read_step_future; eauto. i. des.
      destruct (RegFile.eval_rmw rs1 rmw val) as [? []] eqn: EQ.
      * hexploit progress_write_step; eauto.
        { apply Time.incr_spec. }
        { i. inv READ. s. rewrite PROMISES1. apply Memory.bot_nonsynch_loc. }
        i. des. esplits. econs; [|econs 4]; eauto.
        { econs. econs. rewrite EQ. eauto. }
        { rewrite x0. eauto. }
      * esplits. econs; [|econs 2]; eauto. econs. econs. rewrite EQ; eauto.
    + hexploit progress_fence_step; eauto.
      { i. rewrite PROMISES1. apply Memory.bot_nonsynch. }
      i. des.
      esplits. econs; [|econs 5]; eauto. econs. econs.
    + hexploit progress_fence_step; eauto.
      { i. rewrite PROMISES1. apply Memory.bot_nonsynch. }
      i. des.
      esplits. econs; [|econs 6]; eauto. econs. econs.
    + hexploit Local.bot_promise_consistent; eauto. i.
      destruct (Const.eq_dec (RegFile.eval_expr rs1 e) 0).
      * esplits. econs; [|econs 7]; eauto. econs. econs. ss.
      * esplits. econs; [|econs 1]; eauto. econs. econs. ss.
  - esplits. econs; [|econs 1]; eauto. econs.
  - esplits. econs; [|econs 1]; eauto. econs.
Grab Existential Variables.
  { auto. }
Qed.
