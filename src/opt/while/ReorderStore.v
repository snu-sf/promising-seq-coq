From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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
Require Import Progress.

Require Import FulfillStep.
Require Import LowerPromises.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import Compatibility.

Require Import ReorderStep.
Require Import ReorderAbortCommon.
Require Import ProgressStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_store l1 v1 o1: forall (i2:Instr.t), Prop :=
| reorder_store_load
    r2 l2 o2
    (ORD11: Ordering.le o1 Ordering.relaxed)
    (ORD12: Ordering.le Ordering.plain o1)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_store l1 v1 o1 (Instr.load r2 l2 o2)
| reorder_store_store
    l2 v2 o2
    (ORD11: Ordering.le o1 Ordering.relaxed)
    (ORD12: Ordering.le Ordering.plain o1)
    (ORD2: Ordering.le Ordering.plain o2)
    (LOC: l1 <> l2):
    reorder_store l1 v1 o1 (Instr.store l2 v2 o2)
(* reordering update; store is unsound *)
(* | reorder_store_update *)
(*     r2 l2 rmw2 or2 ow2 *)
(*     (ORD1: Ordering.le o1 Ordering.relaxed) *)
(*     (ORDR2: Ordering.le or2 Ordering.relaxed) *)
(*     (LOC: l1 <> l2) *)
(*     (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1)) (RegSet.singleton r2)): *)
(*     reorder_store l1 v1 o1 (Instr.update r2 l2 rmw2 or2 ow2) *)
.

Inductive sim_store: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                       (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_store_write
    l1 f1 t1 v1 released1 o1 i2 rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src sc2_src
    (REORDER: reorder_store l1 v1 o1 i2)
    (FULFILL: fulfill_step lc1_src sc1_src l1 f1 t1 (RegFile.eval_value rs v1) None released1 o1 lc2_src sc2_src)
    (LOCAL: sim_local SimPromises.bot lc2_src lc1_tgt)
    (SC: TimeMap.le sc2_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_store
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.store l1 v1 o1)]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
| sim_store_racy_write
    l1 v1 o1 i2 rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (REORDER: reorder_store l1 v1 o1 i2)
    (RACY_WRITE: Local.racy_write_step lc1_src mem1_src l1 o1)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_store
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.store l1 v1 o1)]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_store_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_store st_src lc_src sc1_src mem1_src
                       st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt)
      (SC1: TimeMap.le sc2_src sc2_tgt)
      (MEM1: sim_memory mem2_src mem2_tgt)
      (WF_SRC: Local.wf lc_src mem2_src)
      (WF_TGT: Local.wf lc_tgt mem2_tgt)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt)
      (MEM_SRC: Memory.closed mem2_src)
      (MEM_TGT: Memory.closed mem2_tgt):
  sim_store st_src lc_src sc2_src mem2_src
            st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1.
  - exploit future_fulfill_step; try exact FULFILL; eauto; try refl.
    i. des. econs; eauto.
  - exploit future_racy_write_step; try exact RACY_WRITE; eauto.
    i. des. econs 2; eauto.
Qed.

Lemma sim_store_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_store st1_src lc1_src sc1_src mem1_src
                      st1_tgt lc1_tgt sc1_tgt mem1_tgt):
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_store)
                     st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM.
  { (* write *)
    ii.
    exploit fulfill_step_future; eauto; try viewtac. i. des.
    inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
      try (inv STATE; inv INSTR; inv REORDER); ss.
    - (* promise *)
      right.
      exploit Local.promise_step_future; eauto. i. des.
      exploit sim_local_promise; try exact LOCAL0; (try by etrans; eauto); eauto. i. des.
      exploit reorder_fulfill_promise; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; eauto. i. des.
      esplits.
      + ss.
      + eauto.
      + econs 2. econs 1. econs; eauto.
      + auto.
      + etrans; eauto.
      + auto.
      + right. econs; eauto.
        eapply Memory.future_closed_timemap; eauto.
    - (* load *)
      right.
      exploit sim_local_read; try exact LOCAL0; (try by etrans; eauto); eauto; try refl. i. des.
      exploit reorder_fulfill_read; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
      exploit Local.read_step_future; try exact STEP1; eauto. i. des.
      exploit fulfill_write_sim_memory; eauto; try by viewtac. i. des.
      esplits.
      + ss.
      + econs 2; eauto. econs.
        * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
        * auto.
      + econs 2. econs 2. econs; [|econs 3]; eauto. econs.
        erewrite <- RegFile.eq_except_value; eauto.
        * econs.
        * symmetry. eauto.
        * apply RegFile.eq_except_singleton.
      + auto.
      + auto.
      + etrans; eauto.
      + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
    - (* store *)
      right.
      hexploit sim_local_write_bot; try exact LOCAL1;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto; try refl; try by viewtac. i. des.
      hexploit reorder_fulfill_write_sim_memory; try exact FULFILL; try exact STEP_SRC; eauto; try by viewtac. i. des.
      exploit Local.write_step_future; try exact STEP1; eauto; try by viewtac. i. des.
      exploit fulfill_write_sim_memory; eauto; try by viewtac. i. des.
      esplits.
      + ss.
      + econs 2; eauto. econs.
        * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
        * auto.
      + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      + auto.
      + etrans; eauto.
      + etrans; eauto. etrans; eauto.
      + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
        etrans; eauto.
    - (* na write *)
      inv LOCAL1. destruct ord; ss.
    - (* racy read *)
      right.
      exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_fulfill_racy_read; try exact FULFILL; eauto. i. des.
      exploit fulfill_write_sim_memory; eauto. i. des.
      esplits.
      + ss.
      + econs 2; eauto. econs.
        * econs. econs 2. econs; [|econs 9]; eauto. econs. econs.
        * auto.
      + econs 2. econs 2. econs; [|econs 3]; eauto. econs.
        erewrite <- RegFile.eq_except_value; eauto.
        * econs.
        * symmetry. eauto.
        * apply RegFile.eq_except_singleton.
      + auto.
      + ss.
      + etrans; eauto.
      + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
    - (* racy write *)
      left.
      exploit sim_local_racy_write; try exact LOCAL1;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto; try refl. i. des.
      exploit reorder_fulfill_racy_write; try exact FULFILL; eauto. i. des.
      unfold Thread.steps_failure.
      esplits; try refl.
      + econs 2. econs; [|econs 10]; eauto. econs. econs.
      + ss.
  }

  { (* racy write *)
    ii. left. unfold Thread.steps_failure.
    inv REORDER.
    - (* load *)
      exploit progress_read_step_cur; try exact WF_SRC; eauto. i. des.
      exploit read_step_cur_future; try exact READ; eauto. i. des.
      esplits.
      + econs 2; try refl. econs.
        * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
        * ss.
      + econs 2. econs; [|econs 10].
        * econs. econs.
        * inv RACY_WRITE. econs; eauto; try congr.
          { inv RACE. econs. congr. }
          { ii. rewrite <- PROMISES, <- TVIEW in *. eauto. }
      + ss.
    - (* store *)
      exploit (@LowerPromises.steps_promises_rel
                 lang (Thread.mk lang (State.mk rs [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr (Instr.store l1 v1 o1)])
                                 lc1_src sc1_src mem1_src)); s; eauto.
      i. des. destruct e2, state. ss.
      exploit LowerPromises.rtc_opt_promise_step_future; eauto. s. i. des. inv STATE.
      hexploit LowerPromises.promises_rel_promise_consistent; try apply RACY_WRITE; eauto. i.
      hexploit LowerPromises.promises_rel_nonsynch; eauto. i.
      exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
      exploit write_step_consistent; try exact WF2; eauto. i. des.
      esplits.
      + eapply rtc_n1; eauto. econs.
        * econs. econs 2. econs; [|econs 3; eauto]. econs. econs.
        * ss.
      + econs 2. econs; [|econs 10].
        * econs. econs.
        * inv RACY_WRITE.
          exploit Thread.rtc_tau_step_non_promised; try exact STEPS0; eauto. s. i. des.
          exploit Local.program_step_non_promised; [econs 3|..]; try exact STEP; eauto. i. des.
          econs; eauto; try congr.
          inv RACE. econs. rewrite TVIEW in TS.
          inv STEP. ss.
          apply TimeFacts.join_spec_lt; auto.
          unfold TimeMap.singleton, Loc.LocFun.add, Loc.LocFun.init, Loc.LocFun.find. condtac; ss.
          eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
      + ss.
  }
Qed.

Lemma sim_store_sim_thread:
  sim_store <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_store_mon; eauto. i.
    inversion x0.
    { subst.
      exploit (progress_program_step_non_update rs i2 nil); eauto.
      { inv x0; inv REORDER0; ss. }
      i. des.
      destruct th2. exploit sim_store_step; eauto.
      { econs 2. eauto. }
      i. des; eauto.
      + exploit Thread.program_step_promises_bot; eauto. s. i.
        exploit Thread.rtc_tau_step_future; eauto. s. i. des.
        exploit Thread.opt_step_future; eauto. s. i. des.
        exploit Thread.program_step_future; eauto. s. i. des.
        punfold SIM. exploit SIM; try apply SC3; eauto; try refl.
        { exploit Thread.program_step_promises_bot; eauto. s. i.
          eapply Local.bot_promise_consistent; eauto. }
        s. i. des.
        exploit PROMISES; eauto. i. des.
        * left.
          unfold Thread.steps_failure in *. des.
          esplits; [|eauto|]; ss.
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; inv STATE; inv INSTR; inv REORDER. }
        * right.
          esplits; [|eauto].
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; inv STATE; inv INSTR; inv REORDER. }
      + inv SIM; inv STEP; inv STATE.
    }
    { subst.
      exploit (progress_program_step_non_update rs i2 nil); eauto.
      { inv x0; inv REORDER0; ss. }
      i. des.
      destruct th2. exploit sim_store_step; eauto.
      { econs 2. eauto. }
      i. des; eauto.
      + exploit Thread.program_step_promises_bot; eauto. s. i.
        exploit Thread.rtc_tau_step_future; eauto. s. i. des.
        exploit Thread.opt_step_future; eauto. s. i. des.
        exploit Thread.program_step_future; eauto. s. i. des.
        punfold SIM. exploit SIM; try apply SC3; eauto; try refl.
        { exploit Thread.program_step_promises_bot; eauto. s. i.
          eapply Local.bot_promise_consistent; eauto. }
        s. i. des.
        exploit PROMISES; eauto. i. des.
        * left.
          unfold Thread.steps_failure in *. des.
          esplits; [|eauto|]; ss.
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; inv STATE; inv INSTR; inv REORDER. }
        * right.
          esplits; [|eauto].
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; inv STATE; inv INSTR; inv REORDER. }
      + inv SIM; inv STEP; inv STATE.
    }
  - exploit sim_store_mon; eauto. i. des.
    exploit sim_store_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.
