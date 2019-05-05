Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import Simulation.

Set Implicit Arguments.


Lemma tids_find
      tids ths_src ths_tgt
      tid
      (TIDS_SRC: tids = Threads.tids ths_src)
      (TIDS_TGT: tids = Threads.tids ths_tgt):
  (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
  (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
Proof.
  split; i; des.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
Qed.

Lemma thread_rtc_step_rtc_step
      l
      ths1_src sc1_src mem1_src
      sc2_src mem2_src
      ths_tgt sc_tgt mem_tgt
      tid lang_src st1_src lc1_src st2_src lc2_src
      (TIDS: Threads.tids ths1_src = Threads.tids ths_tgt)
      (NOTIN: forall tid' lang_src st_src lc_src
                (FIND: IdentMap.find tid' ths1_src = Some (existT _ lang_src st_src, lc_src))
                (TID: ~ (tid = tid' \/ List.In tid' l)),
          Language.is_terminal _ st_src /\ Local.is_terminal lc_src)
      (IN: forall tid' lang_src st_src lc_src lang_tgt st_tgt lc_tgt
             (TID: tid = tid' \/ List.In tid' l),
          IdentMap.find tid' ths1_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid' ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          exists sim_terminal,
            @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc_tgt mem_tgt)
      (WF_SRC: Configuration.wf (Configuration.mk ths1_src sc1_src mem1_src))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (CONSISTENT_TGT: Configuration.consistent (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (FIND: IdentMap.find tid ths1_src = Some (existT _ lang_src st1_src, lc1_src))
      (STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk lang_src st2_src lc2_src sc2_src mem2_src))
      (MEMORY2: sim_memory mem2_src mem_tgt)
      (SC2: TimeMap.le sc2_src sc_tgt)
      (LOCAL: Local.promises lc2_src = Memory.bot):
  rtc Configuration.tau_step
      (Configuration.mk ths1_src sc1_src mem1_src)
      (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) sc2_src mem2_src).
Proof.
  inv WF_SRC. inv WF. ss. exploit THREADS; eauto. i.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  generalize (rtc_tail STEPS). i. des.
  - inv H0. inv TSTEP. econs; eauto.
    econs. rewrite <- EVENT. econs; ss; eauto.
    unfold Configuration.consistent. s.
    unfold Threads.consistent. i.
    destruct (Ident.eq_dec tid0 tid).
    + subst. rewrite IdentMap.gss in TH.
      inv TH. Configuration.simplify.
      ii. ss. esplits; eauto.
    + rewrite IdentMap.gso in TH; auto.
      destruct (List.In_dec Ident.eq_dec tid0 l); cycle 1.
      { exploit NOTIN; eauto.
        { ii. des; ss. subst. ss. }
        i. des. ii. esplits; eauto. ss. apply x1. }
      destruct (IdentMap.find tid0 ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:FIND_TGT; cycle 1.
      { remember (Threads.tids ths1_src) as tids eqn:TIDS_SRC.
        exploit tids_find; [exact TIDS_SRC|exact TIDS|..]. i. des.
        exploit x1; eauto. i. des. rewrite FIND_TGT in x3. inv x3. }
      exploit IN; eauto. i. des.
      exploit sim_thread_future; try exact x0; try exact SC_FUTURE; try exact MEM_FUTURE; try refl; eauto. i.
      inv WF_TGT. inv WF. ss. exploit THREADS0; eauto. i.
      hexploit sim_thread_consistent; try exact x2; eauto.
      exploit Thread.rtc_tau_step_disjoint; eauto. s. i. des.
      exploit Thread.rtc_tau_step_future; eauto. s. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      auto.
  - inv H.
    replace (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) with ths1_src; auto.
    apply IdentMap.eq_leibniz. ii.
    rewrite -> IdentMap.gsident; auto.
Qed.

Lemma sim_thread_sim
      ths_src sc0_src mem0_src
      ths_tgt sc0_tgt mem0_tgt
      (TIDS: Threads.tids ths_src = Threads.tids ths_tgt)
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          exists sim_terminal,
            @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt)
  :
    sim ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt.
Proof.
  remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
  rename TIDS into TIDS_TGT.
  revert ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt tids TIDS_SRC TIDS_TGT SIM.
  pcofix CIH. i. pfold. ii. splits.
  - (* TERMINAL CASE *)
    assert (NOTIN: forall tid lang_src st_src lc_src
                     (FIND: IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src))
                     (TID: ~ List.In tid (IdentSet.elements tids)),
               Language.is_terminal _ st_src /\ Local.is_terminal lc_src).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - exfalso. apply TID. rewrite IdentSet.mem_spec in MEM.
        rewrite <- IdentSet.elements_spec1 in MEM.
        clear - MEM. induction MEM; [econs 1|econs 2]; auto.
      - rewrite TIDS_SRC in MEM. rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src) eqn:IFIND; [inv MEM|]. ss. }
    assert (IN: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                  (TID: List.In tid (IdentSet.elements tids)),
               IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
               IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
               exists sim_terminal,
                 @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt).
    { eauto. }
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto. }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto. }
    revert NOTIN IN TIDS_MEM NODUP.
    move tids at top. clear SIM. revert_until CIH.
    induction (IdentSet.elements tids); i.
    { esplits; eauto. ii. exploit NOTIN; eauto. }
    destruct (IdentMap.find a ths_src) as [[[lang_src st_src] lc_src]|] eqn:ASRC;
      destruct (IdentMap.find a ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:ATGT; cycle 1.
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x0; eauto. i. des. rewrite ATGT in x. inv x. }
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite ASRC in x. inv x. }
    { exploit IHl; [exact TIDS_SRC|exact TIDS_TGT|exact SC1|exact MEMORY1|..]; eauto; i.
      - eapply NOTIN; eauto. ii. inv H; ss. congr.
      - eapply IN; eauto. econs 2; eauto.
      - eapply TIDS_MEM; eauto. econs 2; eauto.
      - inv NODUP. ss.
    }
    generalize WF_SRC. intro X. inv X. ss. inv WF. exploit THREADS; eauto. i.
    generalize WF_TGT. intro X. inv X. ss. inv WF. exploit THREADS0; eauto. i.
    exploit (IN a); eauto. i. des.
    exploit TERMINAL_TGT; eauto. i. des.
    punfold x2. exploit x2; try exact x; try exact x0; try exact SC; try exact SC0; eauto. i. des.
    exploit TERMINAL; eauto. i. des.
    exploit thread_rtc_step_rtc_step; try exact STEPS; eauto; i.
    { guardH TID. exploit IN; try eapply TID; eauto. i. des.
      esplits. eapply sim_thread_future; try exact x1; eauto. }
    { inv THREAD. eapply sim_local_memory_bot; eauto. }
    exploit Configuration.rtc_step_future; try eapply x3; eauto. s. i. des.
    exploit IHl; [| |exact SC2|exact MEMORY|..]; try exact WF2; try exact WF_TGT;
      try exact SC_FUTURE_TGT; try exact MEM_FUTURE_TGT;
        try (etrans; [exact SC_FUTURE_SRC|exact SC_FUTURE]);
        try (etrans; [exact MEM_FUTURE_SRC|exact MEM_FUTURE]); eauto; i.
    { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
    { rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
      - subst. Configuration.simplify. split; auto.
        inv THREAD. econs. eapply sim_local_memory_bot; eauto.
      - eapply NOTIN; eauto. ii. des; ss. subst. ss. }
    { rewrite IdentMap.gsspec in H. revert H. condtac; ss; i.
      - subst. inv NODUP. congr.
      - exploit IN; eauto. }
    { inv NODUP. ss. }
    des. rewrite x1 in x3.
    esplits; try exact x3; eauto.
  - (* STEP CASE *)
    i. inv STEP_TGT. destruct e2. ss.
    destruct (IdentMap.find tid_tgt ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite FIND_SRC in x. inv x. }
    inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
    exploit SIM; eauto. i. des.
    exploit sim_thread_future; eauto. i.
    exploit sim_thread_plus_step; try exact STEPS; try exact x1; eauto. s. i. des.
    inv STEP0.
    + generalize (rtc_tail STEPS0). intro X. des.
      * inv X0. inv TSTEP. esplits; eauto.
        { rewrite <- EVENT. ss. rewrite <- EVENT0.
          econs 2. econs; eauto. ss.
          unfold Configuration.consistent. s.
          unfold Threads.consistent. i.
          rewrite IdentMap.gsspec in TH. revert TH. condtac; ss; i.
          - inv TH. Configuration.simplify.
            eapply sim_thread_consistent; eauto.
            eapply CONSISTENT; ss. rewrite IdentMap.gss. ss.
          - destruct (IdentMap.find tid ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:FIND_TGT; cycle 1.
            { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
              exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
              exploit x2.
              { esplits; eapply TH. }
              i. des. rewrite FIND_TGT in x4. inv x4. }
            exploit SIM; eauto. i. des.
            exploit sim_thread_future; try exact x0; eauto. i.
            exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
            exploit sim_thread_future; try exact x3;
              try exact SC_FUTURE1; try exact MEM_FUTURE1; try (etrans; eauto). i.
            eapply sim_thread_consistent; try exact x4; eauto.
            { exploit THREADS; eauto. i.
              exploit DISJOINT; [|exact FIND_SRC|exact TH|]; eauto. i.
              exploit Thread.rtc_tau_step_disjoint; try exact STEPS0; eauto. s. i. des. ss. }
            { exploit THREADS0; eauto. i.
              exploit DISJOINT0; [|exact TID|exact FIND_TGT|]; eauto. i.
              exploit Thread.rtc_tau_step_disjoint; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_disjoint; try exact STEP; eauto. s. i. des. ss. }
            { eapply CONSISTENT. s. rewrite IdentMap.gso; eauto. }
        }
        { ss. right. eapply CIH.
          - rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
            rewrite Threads.tids_o. rewrite FIND_SRC. ss.
          - rewrite TIDS_TGT.
            rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
            rewrite Threads.tids_o. rewrite TID. ss.
          - i. Configuration.simplify; [eexists; eauto|].
            exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact X; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
            exploit SIM; try eapply H; eauto. i. des.
            eexists.
            eapply sim_thread_future; try exact x0; try by (etrans; [eauto|etrans; eauto]). }
      * ss. inv X. esplits; eauto.
        { destruct e0; ss. }
        { right. eapply CIH; ss.
          - rewrite TIDS_TGT.
            rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
            rewrite Threads.tids_o. rewrite TID. ss.
          - i. Configuration.simplify.
            + rewrite FIND_SRC in H. inv H. Configuration.simplify.
              eexists; eauto.
            + exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_future; try exact STEP; eauto. s. i. des.
              exploit SIM; try eapply H; eauto. i. des.
              eexists.
              eapply sim_thread_future; try exact x0; eauto; try by (etrans; [eauto|etrans; eauto]). }
    + esplits; eauto.
      * rewrite <- EVENT.
        econs 2. econs; eauto. ss.
        unfold Configuration.consistent. s.
        unfold Threads.consistent. i.
        rewrite IdentMap.gsspec in TH. revert TH. condtac; ss; i.
        { inv TH. Configuration.simplify.
          eapply sim_thread_consistent; eauto.
          eapply CONSISTENT; ss. rewrite IdentMap.gss. ss. }
        { destruct (IdentMap.find tid ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:FIND_TGT; cycle 1.
          { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
            exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
            exploit x2.
            { esplits; eapply TH. }
            i. des. rewrite FIND_TGT in x4. inv x4. }
          exploit SIM; eauto. i. des.
          exploit sim_thread_future; try exact x0; eauto. i.
          exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP; eauto. s. i. des.
          exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP1; eauto. s. i. des.
          exploit sim_thread_future; try exact x3; try by etrans; eauto. i.
          eapply sim_thread_consistent; try exact x4; eauto.
          { exploit THREADS; eauto. i.
            exploit DISJOINT; [|exact FIND_SRC|exact TH|]; eauto. i.
            exploit Thread.rtc_tau_step_disjoint; try exact STEPS0; eauto. s. i. des.
            exploit Thread.step_disjoint; try exact STEP1; eauto. s. i. des. ss. }
          { exploit THREADS0; eauto. i.
            exploit DISJOINT0; [|exact TID|exact FIND_TGT|]; eauto. i.
            exploit Thread.rtc_tau_step_disjoint; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_disjoint; try exact STEP; eauto. s. i. des. ss. }
          { eapply CONSISTENT. s. rewrite IdentMap.gso; eauto. }
        }
      * ss. right. eapply CIH.
        { rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
          rewrite Threads.tids_o. rewrite FIND_SRC. ss. }
        { rewrite TIDS_TGT.
          rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
          rewrite Threads.tids_o. rewrite TID. ss. }
        { i. Configuration.simplify; [eexists; eauto|].
          exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP; eauto. s. i. des.
          exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP1; eauto. s. i. des.
          exploit SIM; try eapply H; eauto. i. des.
          eexists.
          eapply sim_thread_future; try exact x0; try by (etrans; [eauto|etrans; eauto]). }
Grab Existential Variables.
  { auto. }
Qed.
