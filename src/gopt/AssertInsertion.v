Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import PFStepCommon.
Require Import PFStep.
Require Import PFStepCap.
Require Import Invariant.

Require Import GSimulation.

Set Implicit Arguments.


Inductive opt_lang_step: forall (e:ProgramEvent.t) (st1 st2:State.t), Prop :=
| opt_lang_step_none
    st:
    opt_lang_step ProgramEvent.silent st st
| opt_lang_step_some
    e st1 st2
    (STEP: lang.(Language.step) e st1 st2):
    opt_lang_step e st1 st2
.

Inductive opt_program_step: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
| opt_program_step_none
    e1:
    opt_program_step ThreadEvent.silent e1 e1
| opt_program_step_some
    e e1 e2
    (STEP: Thread.program_step e e1 e2):
    opt_program_step e e1 e2
.

Lemma inj_option_pair
      A B
      (a1 a2: A)
      (b1 b2: B)
      (EQ: Some (a1, b1) = Some (a2, b2)):
  a1 = a2 /\ b1 = b2.
Proof.
  inv EQ. ss.
Qed.

Ltac simplify :=
  repeat
    (try match goal with
         | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
           rewrite IdentMap.Facts.add_o in H
         | [H: context[if ?c then _ else _] |- _] =>
           destruct c
         | [H: Some (_, _) = Some (_, _) |- _] =>
           apply inj_option_pair in H; des
         | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
           apply inj_pair2 in H
         end;
     ss; subst).

Lemma tau_opt_all
      e1 e2 e3 e
      (STEPS: rtc (@Thread.tau_step lang) e1 e2)
      (STEP: Thread.opt_step e e2 e3):
  rtc (@Thread.all_step lang) e1 e3.
Proof.
  induction STEPS.
  - inv STEP; eauto.
    econs 2; eauto. econs. econs. eauto.
  - exploit IHSTEPS; eauto. i.
    econs 2; eauto.
    inv H. inv TSTEP. econs. econs. eauto.
Qed.


Section AssertInsertion.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp)
    (program: Threads.syntax).

  Context `{LOGIC: Logic.t S J program}.


  (* simulation relations on threads *)

  Inductive sim_stmts (tid: Ident.t): forall (stmts_src stmts_tgt: list Stmt.t), Prop :=
  | sim_stmts_nil:
      sim_stmts tid [] []
  | sim_stmts_instr
      (i: Instr.t) stmts_src stmts_tgt
      (SIM: sim_stmts tid stmts_src stmts_tgt):
      sim_stmts tid ((Stmt.instr i)::stmts_src) ((Stmt.instr i)::stmts_tgt)
  | sim_stmts_ite
      cond
      stmts1_src stmts2_src stmts_src
      stmts1_tgt stmts2_tgt stmts_tgt
      (SIM1: sim_stmts tid (stmts1_src ++ stmts_src) (stmts1_tgt ++ stmts_tgt))
      (SIM2: sim_stmts tid (stmts2_src ++ stmts_src) (stmts2_tgt ++ stmts_tgt)):
      sim_stmts tid
                ((Stmt.ite cond stmts1_src stmts2_src)::stmts_src)
                ((Stmt.ite cond stmts1_tgt stmts2_tgt)::stmts_tgt)
  | sim_stmts_dowhile
      cond
      stmts1_src stmts_src
      stmts1_tgt stmts_tgt
      (SIM: sim_stmts tid
                      (stmts1_src ++ (Stmt.ite cond ((Stmt.dowhile stmts1_src cond)::nil) nil) :: stmts_src)
                      (stmts1_tgt ++ (Stmt.ite cond ((Stmt.dowhile stmts1_tgt cond)::nil) nil) :: stmts_tgt)):
      sim_stmts tid
                ((Stmt.dowhile stmts1_src cond)::stmts_src)
                ((Stmt.dowhile stmts1_tgt cond)::stmts_tgt)
  | sim_stmts_assert
      e stmts_src stmts_tgt
      (SIM: sim_stmts tid stmts_src stmts_tgt)
      (SUCCESS: forall rs (SOUND: S tid lang (State.mk rs stmts_src)),
          RegFile.eval_expr rs e <> 0):
      sim_stmts tid stmts_src ((Stmt.instr (Instr.assert e))::stmts_tgt)
  .
  Hint Constructors sim_stmts.

  Inductive sim_state (tid: Ident.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_intro
      (STMTS: sim_stmts tid st_src.(State.stmts) st_tgt.(State.stmts))
      (REGS: st_src.(State.regs) = st_tgt.(State.regs))
  .
  Hint Constructors sim_state.

  Inductive sim_thread (tid: Ident.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: sim_state tid e_src.(Thread.state) e_tgt.(Thread.state))
      (LOCAL: e_src.(Thread.local) = e_tgt.(Thread.local))
      (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
      (MEMORY: e_src.(Thread.memory) = e_tgt.(Thread.memory))
  .
  Hint Constructors sim_thread.


  Lemma sim_state_step
        tid st1_src
        e st1_tgt st2_tgt
        (SIM1: sim_state tid st1_src st1_tgt)
        (STEP: lang.(Language.step) e st1_tgt st2_tgt)
        (EVENT: e <> ProgramEvent.abort):
    exists st2_src,
      <<STEP_SRC: opt_lang_step e st1_src st2_src>> /\
      <<SIM2: sim_state tid st2_src st2_tgt>>.
  Proof.
    destruct st1_src, st1_tgt, st2_tgt.
    inv SIM1. ss. subst.
    inv STMTS.
    - inv STEP.
    - exists (State.mk regs1 stmts_src).
      inv STEP. split; eauto.
      econs 2. econs; eauto.
    - inv STEP. esplits.
      + econs 2. econs; eauto.
      + condtac; eauto.
    - inv STEP. esplits.
      + econs 2. econs; eauto.
      + ss.
    - inv STEP; inv INSTR; ss. esplits.
      + econs 1.
      + ss.
  Qed.

  Lemma sim_thread_promise_step
        tid e1_src
        pf e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.promise_step pf e e1_tgt e2_tgt):
    exists e2_src,
      <<STEP_SRC: Thread.promise_step pf e e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    inv STEP_TGT; ss.
    esplits.
    - econs; eauto.
    - eauto.
  Qed.

  Lemma sim_thread_program_step
        tid e1_src
        e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.program_step e e1_tgt e2_tgt)
        (EVENT: e <> ThreadEvent.abort):
    exists e2_src,
      <<STEP_SRC: opt_program_step e e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    inv STEP_TGT; ss.
    exploit sim_state_step; eauto.
    { destruct e; ss. }
    i. des.
    inv LOCAL; inv STEP_SRC; ss.
    - esplits.
      + econs 1.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
  Qed.

  Lemma sim_thread_step
        tid e1_src
        pf e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.step pf e e1_tgt e2_tgt)
        (EVENT: e <> ThreadEvent.abort):
    exists e2_src,
      <<STEP_SRC: Thread.opt_step e e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    inv STEP_TGT.
    - exploit sim_thread_promise_step; eauto. i. des.
      esplits; eauto.
      econs 2. econs 1. eauto.
    - exploit sim_thread_program_step; eauto. i. des.
      esplits; eauto.
      inv STEP_SRC.
      + econs 1.
      + econs 2. econs 2. eauto.
  Qed.

  Lemma sim_thread_rtc_tau_step
        tid e1_src e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. inv TSTEP.
    exploit sim_thread_step; eauto.
    { destruct e; ss. }
    i. des.
    exploit IHSTEPS_TGT; eauto. i. des.
    esplits; [|eauto].
    inv STEP_SRC; eauto.
    econs 2; eauto.
    econs; [econs; eauto|ss].
  Qed.

  Lemma sim_thread_rtc_program_step
        tid e1_src e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (tau (@Thread.program_step lang)) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (tau (@Thread.program_step lang)) e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. exploit sim_thread_program_step; eauto.
    { destruct e; ss. }
    i. des.
    exploit IHSTEPS_TGT; eauto. i. des.
    inv STEP_SRC.
    - esplits; eauto.
    - esplits; try exact SIM0. econs 2; eauto.
  Qed.

  Lemma sim_thread_abort_step
        tid e1_src
        pf e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.step pf ThreadEvent.abort e1_tgt e2_tgt):
    (exists e2_src,
        <<STEP_SRC: Thread.step pf ThreadEvent.abort e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists e stmts,
        <<STMTS: e1_tgt.(Thread.state).(State.stmts) = (Stmt.instr (Instr.assert e))::stmts>> /\
        <<ASSERT: forall (SOUND: S tid lang e1_src.(Thread.state)),
            RegFile.eval_expr e1_src.(Thread.state).(State.regs) e <> 0>>).
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    destruct state, state0. inv STATE. ss. subst.
    inv STEP_TGT; inv STEP; ss.
    inv STATE. inv INSTR. inv STMTS.
    - left. esplits.
      + econs 2. econs; eauto. ss. econs; eauto. econs; eauto.
      + econs; eauto.
    - right. esplits; eauto.
  Qed.

  Lemma sim_thread_steps_abort
        tid e1_src e1_tgt
        pf e2_tgt e3_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (ABORT_TGT: Thread.step pf ThreadEvent.abort e2_tgt e3_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>> /\
      ((exists e3_src,
           <<ABORT_SRC: Thread.step pf ThreadEvent.abort e2_src e3_src>> /\
           <<SIM3: sim_thread tid e3_src e3_tgt>>) \/
       (exists e stmts,
           <<STMTS: e2_tgt.(Thread.state).(State.stmts) = (Stmt.instr (Instr.assert e))::stmts>> /\
           <<ASSERT: forall (SOUND: S tid lang e2_src.(Thread.state)),
               RegFile.eval_expr e2_src.(Thread.state).(State.regs) e <> 0>>)).
  Proof.
    exploit sim_thread_rtc_tau_step; eauto. i. des.
    exists e2_src. splits; auto.
    exploit sim_thread_abort_step; try exact SIM2; eauto.
  Qed.


  (* simulation relation on configurations *)

  Inductive sim_conf (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (SEM: sem S J c_src)
      (TIDS: Threads.tids c_src.(Configuration.threads) = Threads.tids c_tgt.(Configuration.threads))
      (FIND_SRC: forall tid l st_src lc_src
                   (FIND: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ l st_src, lc_src)),
          l = lang)
      (FIND_TGT: forall tid l st_tgt lc_tgt
                   (FIND: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ l st_tgt, lc_tgt)),
          l = lang)
      (THREADS: forall tid st_src lc_src st_tgt lc_tgt
                  (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
                  (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)),
          <<STATE: sim_state tid st_src st_tgt>> /\
          <<LOCAL: lc_src = lc_tgt>>)
      (SC: c_src.(Configuration.sc) = c_tgt.(Configuration.sc))
      (MEMORY: c_src.(Configuration.memory) = c_tgt.(Configuration.memory))
  .
  Hint Constructors sim_conf.


  Lemma tids_find
        ths_src ths_tgt tid
        (TIDS: Threads.tids ths_src = Threads.tids ths_tgt):
    (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    split; i; des.
    - destruct (IdentSet.mem tid (Threads.tids ths_src)) eqn:MEM.
      + rewrite TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
    - destruct (IdentSet.mem tid (Threads.tids ths_tgt)) eqn:MEM.
      + rewrite <- TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
  Qed.

  Lemma sim_conf_find
        c_src c_tgt tid
        (SIM: sim_conf c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread
        c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf c_src c_tgt)
        (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)):
    sim_thread tid
               (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
               (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory)).
  Proof.
    inv SIM. exploit THREADS; eauto. i. des.
    econs; eauto.
  Qed.

  Theorem sim_conf_sim
          c_src c_tgt
          (SIM: sim_conf c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      exploit sim_conf_find; eauto. i. des.
      exploit x0; eauto. i. des.
      inv SIM. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      exploit THREADS; eauto. i. des. subst.
      exploit TERMINAL_TGT; eauto. i. des.
      split; auto.
      destruct st, st_tgt; ss. inv STATE0. ss. subst.
      inv STATE. inv STMTS. ss.
    }
    inv STEP_TGT.
    { (* abort step *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1 mem1].
      dup SIM. inv SIM0. ss. subst.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT THREADS.
      exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
      exploit sim_thread_steps_abort; eauto. i. des.
      - destruct e3_src. ss.
        assert (STEP_SRC: Configuration.step
                            MachineEvent.abort tid
                            (Configuration.mk ths1_src sc1 mem1)
                            (Configuration.mk
                               (IdentMap.add tid (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                               sc memory)).
        { econs 1; eauto. }
        esplits; [econs 2; eauto|].
        right. apply CIH. econs; ss; try by (inv SIM3; ss).
        + eapply configuration_step_sem; try exact STEP_SRC; eauto.
        + repeat rewrite Threads.tids_add.
          repeat rewrite IdentSet.add_mem; ss.
          * rewrite Threads.tids_o. rewrite TID. ss.
          * rewrite Threads.tids_o. rewrite x. ss.
        + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          * inv FIND. ss.
          * inv SIM. eapply FIND_SRC; eauto.
        + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          * inv FIND. ss.
          * inv SIM. eapply FIND_TGT; eauto.
        + i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
          * subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
            simplify. inv SIM3. ss.
          * revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
            inv SIM. eauto.
      - exfalso.
        dup WF_TGT. inv WF_TGT0. inv WF. ss. clear DISJOINT.
        exploit THREADS; eauto. intro WF1_TGT. clear THREADS.
        dup WF_SRC. inv WF_SRC0. inv WF. ss. clear DISJOINT.
        exploit THREADS; eauto. intro WF1_SRC. clear THREADS.
        exploit Thread.rtc_tau_step_future; eauto. s. i. des.
        exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
        exploit PFStep.thread_rtc_tau_step; try exact SIM0; eauto.
        { inv STEP; inv STEP0. inv LOCAL. inv LOCAL0. ss.
          inv SIM2. ss. rewrite LOCAL. ss. }
        i. des.
        inv SEM. ss. exploit TH; eauto. i.
        exploit thread_rtc_tau_step_sem; try exact STEPS_SRC0; eauto.
        { inv SIM0. ss. rewrite STATE. eauto. }
        { eapply vals_incl_sem_memory; eauto.
          eapply PFStep.sim_memory_vals_incl; try eapply SIM0. }
        { eapply PFStep.sim_memory_inhabited; try eapply SIM0; ss.
          - apply WF1_SRC.
          - apply MEM. }
        i. des.
        inv SIM1. rewrite STATE in *.
        inv STEP; inv STEP0. inv STATE0. inv INSTR. inv STMTS.
        inv SIM2. ss. inv STATE0. ss. subst.
        eapply ASSERT; eauto.
    }
    (* normal step *)
    exploit sim_conf_find; eauto. i. des.
    exploit x1; eauto. i. des. clear x0 x1.
    destruct c_src as [ths1_src sc1_src mem1_src].
    destruct c_tgt as [ths1_tgt sc1 mem1].
    dup SIM. inv SIM0. ss. subst.
    exploit FIND_SRC; eauto. i. subst.
    exploit FIND_TGT; eauto. i. subst.
    clear FIND_SRC FIND_TGT THREADS.
    exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
    dup WF_TGT. inv WF_TGT0. inv WF. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF1_TGT. clear THREADS.
    dup WF_SRC. inv WF_SRC0. inv WF. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF1_SRC. clear THREADS.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    exploit Memory.cap_exists; try exact CLOSED0. i. des.
    exploit Memory.cap_closed; eauto. intro CLOSED_CAP.
    exploit Local.cap_wf; try exact WF0; eauto. intro WF_CAP.
    exploit Memory.max_full_timemap_exists; try apply CLOSED_CAP. i. des.
    hexploit Memory.max_full_timemap_closed; try exact x1; eauto. intro SC_MAX.
    exploit CONSISTENT; eauto. s. i. des.
    { (* abort certification *)
      exploit sim_thread_rtc_tau_step; try exact STEPS; eauto. i. des.
      exploit sim_thread_step; try exact STEP; eauto. i. des.
      destruct e2_src0.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e0) tid
                       (Configuration.mk ths1_src sc1 mem1)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                          sc memory)).
      { assert (CONSISTENT_SRC: Thread.consistent (Thread.mk lang state local sc memory)).
        { dup SIM0. inv SIM1. ss. subst. ii. ss. left.
          exploit Memory.cap_inj; [exact CAP|exact CAP0|..]; eauto. i. subst.
          exploit Memory.max_full_timemap_inj; [exact x1|exact SC_MAX0|..]. i. subst.
          unfold Thread.steps_abort in *. des.
          exploit (@sim_thread_steps_abort tid (Thread.mk lang state lc3 sc0 mem0));
            try exact STEPS0; try exact ABORT0; eauto.
          i. des; try by (esplits; eauto).
          exfalso.
          exploit tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit Thread.rtc_tau_step_future; try exact x2; eauto. s. i. des.
          exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
          exploit PFStep.thread_rtc_all_step; try exact x2; eauto.
          { hexploit consistent_promise_consistent; eauto. }
          i. des.
          exploit PFStepCap.sim_thread_exists; try exact SIM4; eauto. s. i. des.
          exploit PFStepCap.thread_rtc_tau_step; try exact STEPS_SRC0; eauto.
          { inv SIM1. rewrite LOCAL.
            inv ABORT0; inv STEP0. inv LOCAL0. inv LOCAL1. ss. }
          i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit thread_rtc_all_step_sem; try exact STEPS_SRC; eauto.
          { inv SIM3. ss. rewrite STATE0. eauto. }
          { eapply vals_incl_sem_memory; eauto.
            eapply PFStep.sim_memory_vals_incl; try eapply SIM3. }
          { eapply PFStep.sim_memory_inhabited; try eapply SIM3; ss.
            - apply WF1_SRC.
            - apply MEM. }
          i. des.
          exploit thread_rtc_pf_step_sem; try exact STEPS_SRC2; eauto; s.
          { eapply vals_incl_sem_memory; eauto. }
          { eapply PFStepCap.sim_memory_inhabited; try eapply SIM5.
            - apply WF0.
            - eapply Memory.cap_closed; eauto. }
          i. des.
          inv SIM6. rewrite STATE0 in *.
          inv ABORT0; inv STEP0. inv STATE1. inv INSTR. inv STMTS.
          inv SIM1. ss. inv STATE1. ss. subst.
          eapply ASSERT; eauto.
        }
        inv STEP_SRC.
        - generalize (rtc_tail STEPS_SRC). i. des.
          + inv H0. inv TSTEP. ss. rewrite <- EVENT0.
            econs 2. econs; try exact x; try exact H; eauto.
            destruct e; ss.
          + inv H. ss.
            replace (IdentMap.add
                       tid
                       (existT (fun lang:language => lang.(Language.state)) lang state, local)
                       ths1_src)
              with ths1_src; eauto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs 2; try exact x; try exact H; eauto.
      }
      esplits; eauto.
      right. apply CIH. econs; ss; try by (inv SIM0; ss).
      - inv CSTEP; ss.
        + repeat rewrite <- H. ss.
        + eapply configuration_step_sem; try exact STEP0; eauto.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite x. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          simplify. inv SIM0. ss.
        + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          inv SIM. eauto.
    }
    { (* normal certification *)
      exploit sim_thread_rtc_tau_step; try exact STEPS; eauto. i. des.
      exploit sim_thread_step; try exact STEP; eauto. i. des.
      destruct e2_src0.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e0) tid
                       (Configuration.mk ths1_src sc1 mem1)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => lang.(Language.state)) lang state, local) ths1_src)
                          sc memory)).
      { inv STEP_SRC.
        - generalize (rtc_tail STEPS_SRC). i. des.
          + inv H0. inv TSTEP. ss. rewrite <- EVENT0.
            econs 2. econs; try exact x; try exact H; eauto.
            * destruct e; ss.
            * ii. right.
              destruct e2. ss. dup SIM0. inv SIM1. ss. subst.
              exploit Memory.cap_inj; [exact CAP|exact CAP0|..]; eauto. i. subst.
              exploit Memory.max_full_timemap_inj; [exact x1|exact SC_MAX0|..]. i. subst.
              exploit (@sim_thread_rtc_tau_step tid (Thread.mk lang state lc3 sc0 mem0));
                try exact STEPS0; eauto.
              i. des. esplits; eauto.
              inv SIM1. rewrite LOCAL. ss.
          + inv H. ss.
            replace (IdentMap.add
                       tid
                       (existT (fun lang:language => lang.(Language.state)) lang state, local)
                       ths1_src)
              with ths1_src; eauto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs 2; try exact x; try exact H; eauto.
          ii. right.
          destruct e2. ss. dup SIM0. inv SIM1. ss. subst.
          exploit Memory.cap_inj; [exact CAP|exact CAP0|..]; eauto. i. subst.
          exploit Memory.max_full_timemap_inj; [exact x1|exact SC_MAX0|..]. i. subst.
          exploit (@sim_thread_rtc_tau_step tid (Thread.mk lang state lc3 sc0 mem0));
            try exact STEPS0; eauto.
          i. des. esplits; eauto.
          inv SIM1. rewrite LOCAL. ss.
      }
      esplits; eauto.
      right. apply CIH. econs; ss; try by (inv SIM0; ss).
      - inv CSTEP; ss.
        + repeat rewrite <- H. ss.
        + eapply configuration_step_sem; try exact STEP0; eauto.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite x. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          simplify. inv SIM0. ss.
        + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          inv SIM. eauto.
    }
  Qed.


  (* assert insertion *)

  Definition syntax_tids (pgm: Threads.syntax): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements pgm).

  Lemma syntax_tids_o tid pgm:
    IdentSet.mem tid (syntax_tids pgm) = IdentMap.find tid pgm.
  Proof.
    unfold syntax_tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements pgm); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b, IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congr.
  Qed.

  Inductive insert_assert (program_tgt: Threads.syntax): Prop :=
  | insert_assert_intro
      (TIDS: syntax_tids program_tgt = syntax_tids program)
      (FIND_SRC: forall tid l syn_src
                   (FIND: IdentMap.find tid program = Some (existT _ l syn_src)),
          l = lang)
      (FIND_TGT: forall tid l syn_tgt
                   (FIND: IdentMap.find tid program_tgt = Some (existT _ l syn_tgt)),
          l = lang)
      (THREADS: forall tid syn_src syn_tgt
                  (FIND_SRC: IdentMap.find tid program = Some (existT _ lang syn_src))
                  (FIND_TGT: IdentMap.find tid program_tgt = Some (existT _ lang syn_tgt)),
          sim_stmts tid syn_src syn_tgt)
  .

  Theorem init_sim_conf
          program_tgt
          (INSERT: insert_assert program_tgt):
    sim_conf (Configuration.init program) (Configuration.init program_tgt).
  Proof.
    inv INSERT. econs; ss; i.
    - apply init_sem; ss.
    - apply IdentSet.ext. i.
      repeat rewrite Threads.tids_o.
      unfold Threads.init.
      repeat rewrite IdentMap.Facts.map_o.
      specialize (@syntax_tids_o i program). i.
      specialize (@syntax_tids_o i program_tgt). i.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt) eqn:TGT; ss.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program = IdentMap.find i program) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program = IdentMap.find i program) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_SRC; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_TGT; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:TGT; ss.
      destruct s, s0; ss.
      inv FIND_SRC0. inv FIND_TGT0. split; ss. simplify.
      unfold State.init. econs; ss.
      eapply THREADS; eauto.
  Qed.
End AssertInsertion.
