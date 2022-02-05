Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import MemoryProps.

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Require Import MaxView.
Require Import Delayed.

Require Import Lia.

Require Import JoinedView.
Require Import SeqLift.
Require Import SeqLiftStep.
Require Import SeqLiftCertification.
Require Import DelayedSimulation.
Require Import Simple.

Require Import Pred.

Require Import SimAux.
Require Import FlagAux.
Require Import SeqAux.

Variant initial_finalized: Messages.t :=
  | initial_finalized_intro
      loc
    :
    initial_finalized loc Time.bot Time.bot Message.elt
.

Lemma configuration_initial_finalized s
  :
  finalized (Configuration.init s) = initial_finalized.
Proof.
  extensionality loc.
  extensionality from.
  extensionality to.
  extensionality msg.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  { inv H. ss. unfold Memory.init, Memory.get in GET.
    rewrite Cell.init_get in GET. des_ifs. }
  { inv H. econs; eauto. i. ss. unfold Threads.init in *.
    rewrite IdentMap.Facts.map_o in TID. unfold option_map in *. des_ifs.
  }
Qed.

Definition initial_mapping: Mapping.t :=
  Mapping.mk
    (fun v ts =>
       if PeanoNat.Nat.eq_dec v 0 then
         if (Time.eq_dec ts Time.bot) then Some (Time.bot)
         else None
       else None)
    0
    (fun _ ts => ts = Time.bot)
.

Definition initial_vers: versions :=
  fun loc ts =>
    if (Time.eq_dec ts Time.bot) then Some (fun _ => 0) else None.

Require Import Program.

Module CertOracle.
  Definition t := Loc.t -> Const.t.

  Definition output (e: ProgramEvent.t): Oracle.output :=
    Oracle.mk_output
      (if is_accessing e then Some Perm.high else None)
      (if is_acquire e then Some (fun _ => Perm.low, fun _ => Const.undef) else None)
      (if is_release e then Some (fun _ => Perm.high) else None)
  .

  Variant step (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (vs: t): t -> Prop :=
    | step_read
        loc ord
        (EVENT: e = ProgramEvent.read loc (vs loc) ord)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
    | step_write
        loc val ord
        (EVENT: e = ProgramEvent.write loc val ord)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0)
    | step_update
        loc valw ordr ordw
        (EVENT: e = ProgramEvent.update loc (vs loc) valw ordr ordw)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs (fun loc0 => if Loc.eq_dec loc0 loc then valw else vs loc0)
    | step_fence
        ordr ordw
        (EVENT: e = ProgramEvent.fence ordr ordw)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
    | step_syscall
        ev
        (EVENT: e = ProgramEvent.syscall ev)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
  .

  Definition to_oracle (vs: t): Oracle.t := @Oracle.mk t step vs.

  Lemma to_oracle_wf vs: Oracle.wf (to_oracle vs).
  Proof.
    revert vs. pcofix CIH. i. pfold. econs.
    { i. dependent destruction STEP. inv STEP.
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
    }
    { i. exists (vs loc). splits.
      { econs. esplits.
        { econs. eapply step_read; eauto. }
        { red. splits; ss; des_ifs. }
      }
      { i. econs. esplits.
        { econs. eapply step_update; eauto. }
        { red. splits; ss; des_ifs. }
      }
    }
    { i. econs. esplits.
      { econs. eapply step_write; eauto. }
      { red. splits; ss; des_ifs. }
    }
    { i. econs. esplits.
      { econs. eapply step_fence; eauto. }
      { red. splits; ss; des_ifs. }
    }
    { i. econs. esplits.
      { econs. eapply step_syscall; eauto. }
      { red. splits; ss; des_ifs. }
    }
  Qed.
End CertOracle.


Section LIFT.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.
  Hypothesis LOCDISJOINT: forall loc (NA: loc_na loc) (AT: loc_at loc), False.

  Definition _nomix
             (nomix: forall (lang: language) (st: lang.(Language.state)), Prop)
             (lang: language) (st: lang.(Language.state)): Prop :=
    forall st1 e
           (STEP: lang.(Language.step) e st st1),
      (<<NA: forall l c (NA: is_atomic_event e = false) (ACC: is_accessing e = Some (l, c)), loc_na l>>) /\
        (<<AT: forall l c (AT: is_atomic_event e = true) (ACC: is_accessing e = Some (l, c)), loc_at l>>) /\
        (<<CONT: nomix lang st1>>)
  .

  Definition nomix := paco2 _nomix bot2.
  Arguments nomix: clear implicits.

  Lemma nomix_mon: monotone2 _nomix.
  Proof.
    ii. exploit IN; eauto. i. des. splits.
    { i. hexploit NA; eauto. }
    { i. hexploit AT; eauto. }
    { auto. }
  Qed.
  #[local] Hint Resolve nomix_mon: paco.


  Definition sim_seq_interference lang_src lang_tgt sim_terminal p0 D st_src st_tgt :=
    forall p1 (PERM: Perms.le p1 p0),
      @sim_seq lang_src lang_tgt sim_terminal p1 D st_src st_tgt.

  Lemma sim_seq_interference_mon lang_src lang_tgt sim_terminal p0 D st_src st_tgt
        (SIM: @sim_seq_interference _ _ sim_terminal p0 D st_src st_tgt)
        p1 (PERM: Perms.le p1 p0)
    :
    @sim_seq_interference lang_src lang_tgt sim_terminal p1 D st_src st_tgt.
  Proof.
    ii. eapply SIM. etrans; eauto.
  Qed.

  Lemma sim_seq_interference_sim_seq lang_src lang_tgt sim_terminal p D st_src st_tgt
        (SIM: @sim_seq_interference _ _ sim_terminal p D st_src st_tgt)
    :
    @sim_seq lang_src lang_tgt sim_terminal p D st_src st_tgt.
  Proof.
    eapply SIM. refl.
  Qed.

  Lemma sim_seq_release lang_src lang_tgt sim_terminal
        p0 d0 st_src0 st_tgt0
        (SIM: sim_seq_at_step_case (@sim_seq lang_src lang_tgt sim_terminal) p0 d0 st_src0 st_tgt0)
    :
    forall st_tgt1 e_tgt
           (STEP_TGT: lang_tgt.(Language.step) e_tgt st_tgt0.(SeqState.state) st_tgt1)
           (ATOMIC: is_atomic_event e_tgt)
           (RELEASE: is_release e_tgt),
    exists st_src1 st_src2 e_src,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
        (<<STEP: lang_src.(Language.step) e_src st_src1.(SeqState.state) st_src2>>) /\
        (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
        (<<SIM: forall i_tgt o p1 mem_tgt
                       (INPUT: SeqEvent.wf_input e_tgt i_tgt)
                       (OUTPUT: Oracle.wf_output e_tgt o)
                       (STEP_TGT: SeqEvent.step i_tgt o p0 st_tgt0.(SeqState.memory) p1 mem_tgt),
          exists i_src mem_src d1,
            (<<STEP_SRC: SeqEvent.step i_src o p0 st_src1.(SeqState.memory) p1 mem_src>>) /\
              (<<MATCH: SeqEvent.input_match d0 d1 i_src i_tgt>>) /\
              (<<INPUT: SeqEvent.wf_input e_src i_src>>) /\
              (<<SIM: sim_seq_interference
                        _ _ sim_terminal
                        p1 d1
                        (SeqState.mk _ st_src2 mem_src)
                        (SeqState.mk _ st_tgt1 mem_tgt)>>)>>).
  Proof.
    i. exploit SIM; eauto. i. des. esplits; eauto.
    i. hexploit SIM0; eauto. i. des. esplits; eauto.
    inv STEP_TGT0. inv REL.
    { red in OUTPUT. des. hexploit RELEASE1; eauto.
      i. rewrite <- H in *. ss.
    }
    ii.
    hexploit (SIM0 i_tgt (Oracle.mk_output o.(Oracle.out_access) o.(Oracle.out_acquire) (Some p1))); eauto.
    { red in OUTPUT. des. red. splits; auto. }
    { econs.
      { eauto. }
      { eauto. }
      { ss. rewrite <- H0. econs 2; eauto. }
    }
  Admitted.

  Definition world := (Mapping.ts * versions * Memory.t)%type.

  Definition world_bot: world := (fun _ => initial_mapping, initial_vers, Memory.init).

  Definition world_messages_le (msgs_src msgs_tgt: Messages.t) (w0: world) (w1: world): Prop :=
        match w0, w1 with
        | (f0, vers0, mem_src0), (f1, vers1, mem_src1) =>
            forall (WF: Mapping.wfs f0),
              (<<MAPLE: Mapping.les f0 f1>>) /\ (<<VERLE: versions_le vers0 vers1>>) /\
                (<<MEMSRC: Memory.future_weak mem_src0 mem_src1>>) /\
                (<<FUTURE: map_future_memory f0 f1 mem_src1>>) /\
                (<<WF: Mapping.wfs f1>>)
        end
  .

  Program Instance world_messages_le_PreOrder msgs_src msgs_tgt: PreOrder (world_messages_le msgs_src msgs_tgt).
  Next Obligation.
    unfold world_messages_le. ii. des_ifs. splits.
    { refl. }
    { refl. }
    { refl. }
    { eapply map_future_memory_refl. }
    { auto. }
  Qed.
  Next Obligation.
    unfold world_messages_le. ii. des_ifs. i.
    hexploit H; eauto. i. des.
    hexploit H0; eauto. i. des.
    splits.
    { etrans; eauto. }
    { etrans; eauto. }
    { etrans; eauto. }
    { eapply map_future_memory_trans; eauto. }
    { eauto. }
  Qed.

  Local Existing Instances world_messages_le_PreOrder.

  Lemma world_messages_le_mon:
    forall msgs_src0 msgs_tgt0 msgs_src1 msgs_tgt1 w0 w1
           (LE: world_messages_le msgs_src1 msgs_tgt1 w0 w1)
           (MSGSRC: msgs_src0 <4= msgs_src1)
           (MSGTGT: msgs_tgt0 <4= msgs_tgt1),
      world_messages_le msgs_src0 msgs_tgt0 w0 w1.
  Proof.
    unfold world_messages_le. i. des_ifs.
  Qed.

  Definition sim_memory_lift: forall (w: world) (mem_src mem_tgt:Memory.t), Prop :=
    fun w mem_src mem_tgt =>
      match w with
      | (f, vers, mem_src') =>
          (<<MEMSRC: mem_src = mem_src'>>) /\
            (<<SIM: sim_memory (fun _ => None) f vers mem_src mem_tgt>>)
      end.

  Definition sim_timemap_lift: forall (w: world) (tm_src: TimeMap.t) (tm_tgt: TimeMap.t), Prop :=
    fun w tm_src tm_tgt =>
      match w with
      | (f, vers, _) =>
          (<<SIM: sim_timemap (fun _ => True) f (Mapping.vers f) tm_src tm_tgt>>)
      end.

  Variant sim_val_lift: forall
      (p: Perm.t)
      (sv_src: Const.t) (sv_tgt: Const.t)
      (v_src: option Const.t) (v_tgt: option Const.t), Prop :=
    | sim_val_lift_low
        sv_src sv_tgt
      :
      sim_val_lift Perm.low sv_src sv_tgt None None
    | sim_val_lift_high
        sv_src sv_tgt v_src v_tgt
        (VALSRC: Const.le sv_src v_src)
        (VALTGT: Const.le v_tgt sv_tgt)
      :
      sim_val_lift Perm.high sv_src sv_tgt (Some v_src) (Some v_tgt)
  .

  Definition sim_vals_lift
             (p: Perms.t) (svs_src: ValueMap.t) (svs_tgt: ValueMap.t)
             (vs_src: Loc.t -> option Const.t) (vs_tgt: Loc.t -> option Const.t): Prop :=
    forall loc (NA: loc_na loc), sim_val_lift (p loc) (svs_src loc) (svs_tgt loc) (vs_src loc) (vs_tgt loc).

  Variant sim_flag_lift
          (d: Flag.t) (sflag_src: Flag.t) (sflag_tgt: Flag.t)
          (flag_src: option Time.t) (flag_tgt: option Time.t): Prop :=
    | sim_flag_lift_intro
        (TGT: flag_tgt -> Flag.join flag_src (Flag.join d sflag_tgt))
        (SRC: sflag_src = flag_src)
  .

  Definition sim_flags_lift
             (d: Flags.t) (sflag_src: Flags.t) (sflag_tgt: Flags.t)
             (flag_src: Loc.t -> option Time.t) (flag_tgt: Loc.t -> option Time.t): Prop :=
    forall loc, sim_flag_lift (d loc) (sflag_src loc) (sflag_tgt loc) (flag_src loc) (flag_tgt loc).

  Variant sim_state_lift:
    forall (w: world)
           (smem_src: SeqMemory.t) (smem_tgt: SeqMemory.t)
           (p: Perms.t)
           (D: Flags.t)
           (mem_src: Memory.t)
           (mem_tgt: Memory.t)
           (lc_src: Local.t)
           (lc_tgt: Local.t)
           (sc_src: TimeMap.t)
           (sc_tgt: TimeMap.t), Prop :=
    | sim_state_lift_intro
        svs_src sflag_src svs_tgt sflag_tgt
        p D f vers flag_src flag_tgt vs_src vs_tgt
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
        (SIM: SeqLiftStep.sim_thread f vers flag_src flag_tgt vs_src vs_tgt mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
        (VALS: sim_vals_lift p svs_src svs_tgt vs_src vs_tgt)
        (FLAGS: sim_flags_lift D sflag_src sflag_tgt flag_src flag_tgt)
        (WF: Mapping.wfs f)
        (VERS: versions_wf f vers)
        (VERSIONED: versioned_memory vers mem_tgt)
        (ATLOCS: forall loc (AT: loc_at loc),
            (<<FLAGSRC: flag_src loc = None>>) /\
              (<<FLAGTGT: flag_tgt loc = None>>) /\
              (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc)>>))
      :
      sim_state_lift
        (f, vers, mem_tgt)
        (SeqMemory.mk svs_src sflag_src) (SeqMemory.mk svs_tgt sflag_tgt)
        p D
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
  .

  Lemma rtc_steps_thread_failure lang th0 th1
        (STEPS: rtc (@Thread.tau_step lang) th0 th1)
        (FAILURE: Thread.steps_failure th1)
    :
    Thread.steps_failure th0.
  Proof.
    unfold Thread.steps_failure in *. des. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma sim_lift_tgt_na_write_step:
    forall
      w p D smem_src smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      mem_tgt1 lc_tgt1 sc_tgt1
      loc from to val msgs kinds kind
      (LIFT: sim_state_lift w smem_src smem_tgt0 p D mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val Ordering.na lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (NALOCS: loc_na loc)
      (LOWER: mem_tgt1 = mem_tgt0)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt0)
      lang_src st_src,
    exists lc_src1 mem_src1 sc_src1 me smem_tgt1,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: SeqState.na_local_step p me (ProgramEvent.write loc val Ordering.na) smem_tgt0 smem_tgt1>>) /\
        (<<LIFT: forall (NORMAL: me <> MachineEvent.failure),
            sim_state_lift w smem_src smem_tgt1 p D mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>)
  .
  Proof.
    i. inv LIFT. destruct (vs_tgt loc) eqn:VAL.
    { hexploit sim_thread_tgt_write_na; eauto. i. des. esplits.
      { eauto. }
      { econs 3; eauto. }
      { i. subst. econs; eauto.
        { ii. unfold ValueMap.write. des_ifs; ss.
          { des_ifs. hexploit (VALS loc); auto. i.
            rewrite VAL in *. rewrite Heq0 in *.
            inv H. econs; eauto. refl.
          }
          { eapply VALS; eauto. }
        }
        { ss. unfold Flags.update. ii. des_ifs.
          { econs; ss; auto.
            { i. destruct (flag_src loc), (D loc); ss. }
            { eapply FLAGS; auto. }
          }
        }
        { i. ss. des_ifs.
          { exfalso. eapply LOCDISJOINT; eauto. }
          { eapply ATLOCS; eauto. }
        }
      }
    }
    { esplits.
      { refl. }
      { econs 3; eauto.}
      { i. hexploit (VALS loc); auto. i.
        rewrite VAL in H. inv H.
        rewrite <- H1 in *. ss.
      }
    }
  Qed.

  Lemma sim_lift_tgt_na_local_step:
    forall
      w p D smem_src smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      e pe mem_tgt1 lc_tgt1 sc_tgt1
      (LIFT: sim_state_lift w smem_src smem_tgt0 p D mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Local.program_step e lc_tgt0 sc_tgt0 mem_tgt0 lc_tgt1 sc_tgt1 mem_tgt1)
      (EVENT: ThreadEvent.get_program_event e = pe)
      (NA: ~ is_atomic_event pe)
      (NALOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_na loc)
      (LOWER: is_na_write e -> mem_tgt1 = mem_tgt0)

      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt0)
      lang_src st_src,
    exists lc_src1 mem_src1 sc_src1 me smem_tgt1,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
      (<<STEP: SeqState.na_local_step p me pe smem_tgt0 smem_tgt1>>) /\
        (<<LIFT: forall (NORMAL: me <> MachineEvent.failure),
            sim_state_lift w smem_src smem_tgt1 p D mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>)
  .
  Proof.
    i. inv STEP; ss.
    { esplits.
      { refl. }
      { econs 1. }
      { eauto. }
    }
    { inv LIFT. destruct ord; ss. hexploit sim_thread_tgt_read_na; eauto.
      i. des. esplits.
      { refl. }
      { econs 2; eauto. i. ss. hexploit (VALS loc); eauto. i. inv H0.
        { des_ifs. }
        hexploit VAL; eauto. i. etrans; eauto.
      }
      { i. econs; eauto. }
    }
    { destruct ord; ss. eapply local_write_step_write_na_step in LOCAL.
      eapply sim_lift_tgt_na_write_step; eauto.
    }
    { esplits.
      { refl. }
      { econs 5. red. destruct ordr, ordw; ss; auto. }
      { ss. }
    }
    { esplits.
      { refl. }
      { econs 4. }
      { ss. }
    }
    { destruct ord; ss. eapply sim_lift_tgt_na_write_step; eauto. }
    { inv LIFT. destruct ord; ss. hexploit sim_thread_tgt_read_na_racy; eauto.
      i. esplits.
      { refl. }
      { econs 2; eauto. i. hexploit (VALS loc); eauto. i.
        rewrite H in H1. inv H1.
        rewrite <- H3 in *. ss.
      }
      { i. econs; eauto. }
    }
    { inv LIFT. destruct ord; ss. hexploit sim_thread_tgt_write_na_racy; eauto.
      i. esplits.
      { refl. }
      { econs 3; eauto. }
      { i. hexploit (VALS loc); eauto. i. rewrite H in H0. inv H0.
        rewrite <- H2 in *. ss.
      }
    }
    { esplits.
      { refl. }
      { econs 5. red. destruct ordr, ordw; ss; auto. }
      { ss. }
    }
  Qed.

  Lemma sim_lift_src_na_local_step:
    forall
      w p D smem_src0 smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      pe me smem_src1
      (LIFT: sim_state_lift w smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (STEP: SeqState.na_local_step p me pe smem_src0 smem_src1)
      (NA: ~ is_atomic_event pe)
      (NALOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_na loc)

      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt)
      lang_src st_src,
    exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 e,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Local.program_step e lc_src1 sc_src1 mem_src1 lc_src2 sc_src2 mem_src2>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me>>) /\
        (<<EVENT: ThreadEvent.get_program_event e = pe>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_lift w smem_src1 smem_tgt p D mem_src2 mem_tgt lc_src2 lc_tgt sc_src2 sc_tgt>>)
  .
  Proof.
    i. inv STEP.
    { esplits.
      { refl. }
      { eapply Local.step_silent. }
      { ss. }
      { ss. }
      { auto. }
    }
    { inv LIFT. ss. hexploit (VALS loc); eauto. i. inv H.
      { hexploit sim_thread_src_read_na_racy; eauto. i.
        esplits.
        { refl. }
        { eapply Local.step_racy_read; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { i. econs; eauto. }
      }
      { hexploit sim_thread_src_read_na.
        { eauto. }
        { eauto. }
        { instantiate (1:=val). etrans; eauto.
          ss. rewrite <- H1 in *. auto.
        }
        { auto. }
        i. des.
        esplits.
        { refl. }
        { eapply Local.step_read; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { i. econs; eauto. }
      }
    }
    { inv LIFT. ss. hexploit (VALS loc); eauto. i. inv H.
      { hexploit sim_thread_src_write_na_racy; eauto.
        i. des. esplits.
        { refl. }
        { eapply Local.step_racy_write; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { ss. }
      }
      { hexploit sim_thread_src_write_na; eauto.
        i. des. esplits.
        { eauto. }
        { eapply Local.step_write_na; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { i. econs; eauto.
          { ss. unfold ValueMap.write. ii. des_ifs.
            { rewrite <- H1. rewrite <- H5. econs; eauto. refl. }
            { eapply VALS; auto. }
          }
          { ss. unfold Flags.update. ii. des_ifs.
          }
          { i. ss. des_ifs.
            { exfalso. eapply LOCDISJOINT; eauto. }
            { eapply ATLOCS; eauto. }
          }
        }
      }
    }
    { inv LIFT. esplits.
      { refl. }
      { eapply Local.step_failure. econs.
        inv SIM. eapply sim_local_consistent; eauto.
      }
      { ss. }
      { ss. }
      { ss. }
    }
    { inv LIFT. esplits.
      { refl. }
      { instantiate (4:=ThreadEvent.racy_update loc valr valw ordr ordw).
        inv SIM. eapply sim_local_consistent in CONSISTENT; eauto.
        eapply Local.step_racy_update. red in ORD. des.
        { econs 1; eauto. }
        { econs 2; eauto. }
      }
      { ss. }
      { ss. }
      { ss. }
    }
  Qed.

  Lemma sim_lift_src_na_step:
    forall
      w p D smem_src0 smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      me smem_src1
      lang_src st_src0 st_src1
      (LIFT: sim_state_lift w smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (STEP: SeqState.na_step p me (SeqState.mk _ st_src0 smem_src0) (SeqState.mk _ st_src1 smem_src1))
      (NOMIX: nomix _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 e pf,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Thread.step pf e (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1) (Thread.mk _ st_src1 lc_src2 sc_src2 mem_src2)>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_lift w smem_src1 smem_tgt p D mem_src2 mem_tgt lc_src2 lc_tgt sc_src2 sc_tgt>>) /\
        (<<NOMIX: nomix _ st_src1>>)
  .
  Proof.
    i. inv STEP.
    punfold NOMIX. exploit NOMIX; eauto. i. des.
    hexploit sim_lift_src_na_local_step; eauto.
    { inv LOCAL; ss.
      { destruct ord; ss. }
      { destruct ord; ss. }
      { red in ORD. des; destruct ordr, ordw; ss. }
    }
    { i. eapply NA; eauto. inv LOCAL; ss.
      { destruct ord; ss. }
      { destruct ord; ss. }
      { red in ORD. destruct ordr, ordw; des; ss. }
    }
    i. des. subst. esplits; eauto.
    { econs 2. econs; eauto. }
    { pclearbot. auto. }
  Qed.

  Lemma sim_lift_src_na_opt_step:
    forall
      w p D smem_src0 smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      me smem_src1
      lang_src st_src0 st_src1
      (LIFT: sim_state_lift w smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (STEP: SeqState.na_opt_step p me (SeqState.mk _ st_src0 smem_src0) (SeqState.mk _ st_src1 smem_src1))
      (NOMIX: nomix _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 e,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Thread.opt_step e (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1) (Thread.mk _ st_src1 lc_src2 sc_src2 mem_src2)>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_lift w smem_src1 smem_tgt p D mem_src2 mem_tgt lc_src2 lc_tgt sc_src2 sc_tgt>>) /\
        (<<NOMIX: nomix _ st_src1>>)
  .
  Proof.
    i. inv STEP.
    { hexploit sim_lift_src_na_step; eauto.
      i. des. esplits; eauto. econs 2; eauto.
    }
    { esplits; eauto.
      { econs 1. }
      { ss. }
    }
  Qed.

  Lemma sim_lift_src_na_steps:
    forall
      lang_src st_src0 st_src1
      p smem_src0 smem_src1
      (STEPS: rtc (SeqState.na_step p MachineEvent.silent) (SeqState.mk _ st_src0 smem_src0) (SeqState.mk _ st_src1 smem_src1))
      w D smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      (LIFT: sim_state_lift w smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (NOMIX: nomix _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists lc_src1 mem_src1 sc_src1,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<LIFT: sim_state_lift w smem_src1 smem_tgt p D mem_src1 mem_tgt lc_src1 lc_tgt sc_src1 sc_tgt>>) /\
        (<<NOMIX: nomix _ st_src1>>)
  .
  Proof.
    intros lang_src st_src0 st_src1 p smem_src0 smem_src1 STEPS.
    remember (SeqState.mk _ st_src0 smem_src0) as th_src0.
    remember (SeqState.mk _ st_src1 smem_src1) as th_src1.
    revert st_src0 st_src1 smem_src0 smem_src1 Heqth_src0 Heqth_src1.
    induction STEPS; i; clarify.
    { esplits.
      { refl. }
      { auto. }
      { auto. }
    }
    destruct y. hexploit sim_lift_src_na_step; eauto. i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    hexploit Thread.step_future; eauto. i. des; ss.
    hexploit LIFT0; eauto.
    { rewrite MACHINE. ss. }
    i. hexploit IHSTEPS; eauto. i. des. esplits.
    { etrans; [eauto|]. econs.
      { econs; eauto. econs; eauto. }
      { eauto. }
    }
    { eauto. }
    { eauto. }
  Qed.

  Variant sim_val_sol_lift: forall (p: Perm.t) (P: bool) (sv: Const.t) (v: Const.t), Prop :=
    | sim_val_sol_lift_high
        sv v
        (VAL: Const.le sv v)
      :
      sim_val_sol_lift Perm.high true sv v
    | sim_val_sol_lift_low
        sv v
      :
      sim_val_sol_lift Perm.low false sv v
  .

  Definition sim_vals_sol_lift (p: Perms.t) (P: Loc.t -> bool) (svs: ValueMap.t) (vs: Loc.t -> Const.t) :=
    forall loc (NA: loc_na loc), sim_val_sol_lift (p loc) (P loc) (svs loc) (vs loc).

  Variant sim_flag_sol_lift (D: Flag.t) (d: bool) (W: Flag.t) (flag: Flag.t): Prop :=
    | sim_flag_sol_lift_intro
        (DEBT: d -> D)
        (WRITTEN: Flag.join W flag -> ~ d)
  .

  Definition sim_flags_sol_lift (D: Flags.t) (d: Loc.t -> bool) (W: Flags.t) (flag: Flags.t): Prop :=
    forall loc, sim_flag_sol_lift (D loc) (d loc) (W loc) (flag loc).

  Variant sim_state_sol_lift (c: bool):
    forall (smem: SeqMemory.t) (p: Perms.t) (D: Flags.t) (W: Flags.t)
           (mem: Memory.t) (lc: Local.t) (sc: TimeMap.t) (o: Oracle.t), Prop :=
    | sim_state_sol_lift_intro
        svs flag
        p P W d D vs ovs
        mem lc sc
        (SIM: sim_thread_sol c vs P d mem lc)
        (VAL: sim_vals_sol_lift p P svs vs)
        (FLAG: sim_flags_sol_lift D d W flag)
        (OVALS: forall loc (NA: loc_at loc), Const.le (ovs loc) (vs loc))
      :
      sim_state_sol_lift
        c
        (SeqMemory.mk svs flag)
        p D W
        mem lc sc (CertOracle.to_oracle ovs)
  .

  Lemma sim_lift_sim_lift_sol c:
    forall
      w p D smem_src smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      lang_src st_src
      (LIFT: sim_state_lift w smem_src smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt)
      (CERTIFIED: c = true -> lc_tgt.(Local.promises) = Memory.bot),
    exists lc_src1 mem_src1 sc_src1 o,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<LIFT: sim_state_sol_lift
                   c smem_src p (Flags.join D smem_tgt.(SeqMemory.flags)) smem_src.(SeqMemory.flags) mem_src1 lc_src1 sc_src1 o>>) /\
        (<<ORACLE: Oracle.wf o>>)
  .
  Proof.
    i. inv LIFT.
    hexploit sim_thread_sim_thread_sol; eauto.
    { instantiate (1:=fun loc => Flag.minus (flag_tgt loc) (flag_src loc)).
      i. ss. destruct (flag_src loc), (flag_tgt loc); ss.
    }
    i. des. esplits; eauto.
    econs; eauto.
    { ii. hexploit (VALS loc); eauto. i. inv H.
      { econs; eauto. }
      { hexploit VALS0; eauto. i. rewrite H. econs; eauto. }
    }
    { ii. ss. hexploit (FLAGS loc); eauto. i. inv H. econs.
      { unfold Flags.minus, Flags.join.
        destruct (D loc), (sflag_tgt loc), (sflag_src loc), (flag_tgt loc), (flag_src loc); auto.
      }
      { unfold Flags.minus, Flags.join. ii.
        destruct (D loc), (sflag_tgt loc), (sflag_src loc), (flag_tgt loc), (flag_src loc); ss.
      }
    }
    { i. refl. }
    { eapply CertOracle.to_oracle_wf. }
  Qed.

  Lemma sim_lift_sol_na_local_step c:
    forall
      p D W smem0 mem0 lc0 sc0 o
      smem1 me pe
      (LIFT: sim_state_sol_lift c smem0 p D W mem0 lc0 sc0 o)
      (STEP: SeqState.na_local_step p me pe smem0 smem1)
      (NALOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_na loc)
      (WF_SRC: Local.wf lc0 mem0)
      (SC_SRC: Memory.closed_timemap sc0 mem0)
      (MEM_SRC: Memory.closed mem0)
      lang st,
    exists lc1 mem1 sc1 lc2 mem2 sc2 e,
      (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st lc0 sc0 mem0) (Thread.mk _ st lc1 sc1 mem1)>>) /\
        (<<STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me \/ ThreadEvent.get_machine_event e = MachineEvent.failure>>) /\
        (<<EVENT: ThreadEvent.get_program_event e = pe>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_sol_lift c smem1 p D W mem2 lc2 sc2 o>>).
  Proof.
    i. inv STEP.
    { esplits.
      { refl. }
      { eapply Local.step_silent. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { inv LIFT. destruct ord; ss.
      hexploit (VAL0 loc); eauto. i. inv H.
      { rewrite <- H1 in *.
        hexploit sim_thread_sol_read_na.
        { eauto. }
        { eauto. }
        { etrans; [eapply VAL; auto|eapply VAL1]. }
        i. des. esplits.
        { refl. }
        { eapply Local.step_read; eauto. }
        { eauto. }
        { ss. }
        { i. econs; eauto. }
      }
      { rewrite <- H1 in *.
        hexploit sim_thread_sol_read_na_racy; eauto.
        { rewrite <- H2. ss. }
        i. des. esplits.
        { refl. }
        { eapply Local.step_racy_read; eauto. }
        { eauto. }
        { ss. }
        { i. econs; eauto. }
      }
    }
    { inv LIFT. destruct ord; ss.
      hexploit (VAL loc); eauto. i. inv H.
      { hexploit sim_thread_sol_write_na; eauto. i. des.
        { esplits.
          { refl. }
          { eapply Local.step_racy_write; eauto. }
          { eauto. }
          { ss. }
          { ss. }
        }
        { esplits.
          { eauto. }
          { eapply Local.step_write_na; eauto. }
          { eauto. }
          { ss. }
          { i. econs; eauto.
            { ii. unfold ValueMap.write. ss. des_ifs.
              { rewrite <- H1. econs. refl. }
              { eapply VAL; auto. }
            }
            { ii. unfold Flags.update. ss. des_ifs.
            }
            { i. ss. des_ifs.
              { exfalso. eapply LOCDISJOINT; eauto. }
              { eapply OVALS; eauto. }
            }
          }
        }
      }
      { hexploit sim_thread_sol_write_na_racy; eauto.
        { rewrite <- H2. ss. }
        i. des. esplits.
        { refl. }
        { eapply Local.step_racy_write; eauto. }
        { eauto. }
        { ss. }
        { ss. }
      }
    }
    { inv LIFT. hexploit sim_thread_sol_failure; eauto. i.
      esplits.
      { refl. }
      { eapply Local.step_failure; eauto. }
      { eauto. }
      { ss. }
      { ss. }
    }
    { inv LIFT. esplits.
      { refl. }
      { eapply Local.step_racy_update.
        instantiate (1:=ordw). instantiate (1:=ordr).
        red in ORD. des.
        { econs 1; eauto. inv SIM. auto. }
        { econs 2; eauto. inv SIM. auto. }
      }
      { auto. }
      { ss. }
      { ss. }
    }
  Qed.

  Lemma perm_meet_high_r p
    :
    Perm.meet p Perm.high = p.
  Proof.
    destruct p; ss.
  Qed.

  Lemma sim_lift_sol_at_step c:
    forall
      D W smem0 mem0 lc0 sc0
      smem1 pe i o
      lang st0 st1 p0 p1 o0 o1
      (LIFT: sim_state_sol_lift c smem0 p0 D W mem0 lc0 sc0 o0)
      (STEP: SeqThread.at_step pe i o (SeqThread.mk (SeqState.mk _ st0 smem0) p0 o0) (SeqThread.mk (SeqState.mk _ st1 smem1) p1 o1))
      (ATLOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_at loc)
      (NUPDATE: ~ is_updating pe)
      (NACQUIRE: ~ is_acquire pe)
      (WF_SRC: Local.wf lc0 mem0)
      (SC_SRC: Memory.closed_timemap sc0 mem0)
      (MEM_SRC: Memory.closed mem0),
    exists lc1 mem1 e sc1 pf,
      (<<STEP: Thread.step pf e (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1)>>) /\
        (<<EVENT: ThreadEvent.get_program_event e = pe>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_sol_lift c smem1 p1 D (Flags.join W (SeqEvent.written i)) mem1 lc1 sc1 o1>>).
  Proof.
    i. inv LIFT. inv STEP. inv MEM.
    assert (exists ovs1,
               (<<ORACLE: o1 = (CertOracle.to_oracle ovs1)>>) /\
                 (<<OSTEP: CertOracle.step e0 i0 o ovs ovs1>>)).
    { dependent destruction ORACLE. esplits; eauto. }
    clear ORACLE. des; clarify.
    red in INPUT0. des. inv ACQ.
    2:{ rewrite <- H0 in *. hexploit ACQUIRE; eauto. i. ss. }
    inv OSTEP; ss; clarify.
    { des_ifs; ss. hexploit OVALS; eauto. i.
      hexploit sim_thread_sol_read; eauto.
      i. des. esplits.
      { econs 2. econs; cycle 1.
        { eapply Local.step_read; eauto. }
        { eauto. }
      }
      { ss. }
      { i. inv REL. inv UPD.
        specialize (UPDATE loc0 v_new). des.
        hexploit UPDATE; eauto. i. inv H2.
        inv MEM. ss. econs; eauto.
        { ii. unfold Perms.update, ValueMap.write.
          destruct (LocSet.Facts.eq_dec loc0 loc), (LocSet.Facts.eq_dec loc loc0); subst; ss; auto.
          econs. auto.
        }
        { ii. unfold SeqEvent.written. rewrite <- H4. rewrite <- H3. ss.
          unfold Flags.add, Flags.join, Flags.update, Flags.bot.
          hexploit (FLAG loc); eauto. i. inv H2.
          destruct (flag loc0) eqn:EQ0, (LocSet.Facts.eq_dec loc loc0); subst; ss.
          { rewrite EQ0 in *. econs; auto. }
          { rewrite flag_join_bot_r. auto. }
          { rewrite EQ0 in *. rewrite flag_join_bot_r. auto. econs; auto. }
          { rewrite flag_join_bot_r. auto. }
        }
      }
    }
    { destruct pe; ss. des. clarify.
      inv UPD. inv MEM. ss. red in INPUT. des. ss.
      rewrite <- H2 in *. ss.
      destruct (Oracle.in_access i0) as [[[loc1 val1] flag1]|] eqn:ACCESS0; ss.
      des; subst. hexploit (UPDATE loc v_new); eauto. i. des.
      hexploit H1; eauto. i. inv H4.
      hexploit sim_thread_sol_write; eauto.
      i. des. esplits.
      { econs 2. econs; cycle 1.
        { eapply Local.step_write; eauto. }
        { eauto. }
      }
      { ss. }
      i. inv REL.
      { ss. econs; eauto.
        { unfold Perms.update, ValueMap.write. ii.
          repeat des_if; subst; ss.
          { econs. refl. }
          { eapply VAL; eauto. }
        }
        { unfold SeqEvent.written. rewrite <- H2. rewrite <- H5.
          ss. rewrite flags_join_bot_r.
          unfold Flags.add, Flags.update, Flags.join, Flags.bot. ii.
          hexploit (FLAG loc0); eauto. i. inv H4. econs; auto.
          destruct (flag loc) eqn:EQ0, (LocSet.Facts.eq_dec loc0 loc); subst.
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
        }
        { i. ss. condtac; subst; auto. }
      }
      { inv MEM. ss.
        destruct (Ordering.le Ordering.strong_relaxed ord0); ss. inv H6.
        econs; eauto.
        { unfold Perms.meet, Perms.update, ValueMap.write. ii.
          repeat condtac; subst; ss.
          { econs. refl. }
          { rewrite perm_meet_high_r. eapply VAL; eauto. }
        }
        { unfold SeqEvent.written. rewrite <- H2. rewrite <- H5. ss.
          unfold Flags.add, Flags.update, Flags.join, Flags.bot. ii.
          hexploit (FLAG loc0); eauto. i. inv H4. econs; auto.
          destruct (flag loc) eqn:EQ0, (LocSet.Facts.eq_dec loc0 loc); subst.
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
        }
        { i. ss. condtac; subst; auto. }
      }
    }
    { destruct pe; ss. }
    { hexploit sim_thread_sol_fence; eauto.
      { instantiate (1:=ordr). destruct ordr, ordw; ss. }
      { instantiate (1:=ordw). destruct ordr, ordw; ss. }
      i. des. esplits.
      { econs 2. econs; cycle 1.
        { eapply Local.step_fence; eauto. }
        { eauto. }
      }
      { ss. }
      i. inv UPD. inv REL.
      { econs; eauto. unfold SeqEvent.written.
        rewrite <- H2. rewrite <- H3. ss.
        rewrite flags_join_bot_r. auto.
      }
      { destruct (Ordering.le Ordering.strong_relaxed ordw); ss. clarify.
        inv MEM. ss. econs; eauto.
        { unfold Perms.meet. ii. rewrite perm_meet_high_r. auto. }
        { unfold SeqEvent.written. rewrite <- H2. rewrite <- H3.
          ss. rewrite flags_join_bot_l. unfold Flags.join, Flags.bot. ii.
          hexploit (FLAG loc); eauto. i. inv H1. econs; auto.
          rewrite flag_join_bot_r. auto.
        }
      }
    }
  Qed.

  Lemma sim_lift_sol_steps c
        tr
        lang st0 st1 smem0 smem1 p0 p1 o0 o1
        (STEPS: SeqThread.steps (@SeqState.na_step _) tr (SeqThread.mk (SeqState.mk _ st0 smem0) p0 o0) (SeqThread.mk (SeqState.mk _ st1 smem1) p1 o1))
    :
    forall mem0 lc0 sc0 w D W
           (LIFT: sim_state_sol_lift c smem0 p0 D W mem0 lc0 sc0 o0)
           (NOMIX: nomix _ st0)
           (TRACE: SeqThread.writing_trace tr w)
           (WF_SRC: Local.wf lc0 mem0)
           (SC_SRC: Memory.closed_timemap sc0 mem0)
           (MEM_SRC: Memory.closed mem0),
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st0 lc0 sc0 mem0)>>) \/
        exists lc1 mem1 sc1,
          (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1)>>) /\
            (<<LIFT: sim_state_sol_lift c smem1 p1 D (Flags.join w W) mem1 lc1 sc1 o1>>) /\
            (<<NOMIX: nomix _ st1>>)
  .
  Proof.
    remember (SeqThread.mk (SeqState.mk _ st0 smem0) p0 o0) as th0.
    remember (SeqThread.mk (SeqState.mk _ st1 smem1) p1 o1) as th1.
    revert st0 st1 smem0 smem1 p0 p1 o0 o1 Heqth0 Heqth1. induction STEPS; i; clarify.
    { inv TRACE. right. esplits.
      { refl. }
      { rewrite flags_join_bot_l. auto. }
      { auto. }
    }
    { inv STEP. inv STEP0. hexploit sim_lift_sol_na_local_step; eauto.
      { punfold NOMIX. exploit NOMIX; eauto. i. des.
        eapply NA in ACCESS; auto. inv LOCAL; ss.
        { destruct ord; ss. }
        { destruct ord; ss. }
      }
      i. ss. des; subst.
      { assert (STEPS1: rtc (@Thread.tau_step _) (Thread.mk _ st0 lc0 sc0 mem0) (Thread.mk _ st4 lc2 sc2 mem2)).
        { etrans; [eauto|]. econs; [|refl]. econs; eauto.
          econs. econs 2; eauto. econs; eauto.
        }
        clear STEPS0 STEP.
        hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
        hexploit LIFT0.
        { rewrite MACHINE. ss. }
        i. hexploit IHSTEPS; eauto.
        { punfold NOMIX. exploit NOMIX; eauto. i. des. pclearbot. auto. }
        i. des.
        { left. eapply rtc_steps_thread_failure; eauto. }
        { right. esplits.
          { etrans; eauto. }
          { eauto. }
          { auto. }
        }
      }
      { left. splits. red. esplits; eauto.
        econs 2. econs; eauto.
      }
    }
    { destruct th1. destruct state0. inv TRACE.
      hexploit sim_lift_sol_at_step; eauto.
      { inv STEP. punfold NOMIX. exploit NOMIX; eauto. i. des.
        eapply AT in ACCESS; auto.
      }
      i. ss. des; subst.
      { destruct (ThreadEvent.get_machine_event e0) eqn:EVENT.
        { assert (STEP1: rtc (@Thread.tau_step _) (Thread.mk _ st0 lc0 sc0 mem0) (Thread.mk _ state0 lc1 sc1 mem1)).
          { econs; [|refl]. econs; eauto. econs; eauto. }
          hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
          hexploit LIFT0; ss.
          i. hexploit IHSTEPS; eauto.
          { punfold NOMIX. inv STEP. exploit NOMIX; eauto. i. des. pclearbot. auto. }
          i. des.
          { left. eapply rtc_steps_thread_failure; eauto. }
          { right. esplits.
            { etrans; eauto. }
            { replace (Flags.join (Flags.join (SeqEvent.written i) w0) W) with
                (Flags.join w0 (Flags.join W (SeqEvent.written i))); auto.
              unfold Flags.join. extensionality loc.
              destruct (w0 loc), (W loc), (SeqEvent.written i loc); auto.
            }
            { auto. }
          }
        }
        { destruct e0; ss. }
        { left. splits. red. esplits; [refl| |eauto].
          replace pf with true in STEP0; eauto.
          inv STEP0; ss. inv STEP1; ss.
        }
      }
    }
  Qed.

  Lemma sim_lift_failure_case:
    forall
      w p D smem_src smem_tgt mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      lang st
      (LIFT: sim_state_lift w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (FAILURE: sim_seq_failure_case p (SeqState.mk _ st smem_src))
      (NOMIX: nomix _ st)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt),
      (<<FAILURE: Thread.steps_failure (Thread.mk lang st lc_src sc_src mem_src)>>).
  Proof.
    i. hexploit sim_lift_sim_lift_sol; eauto.
    { instantiate (1:=false). ss. }
    i. des.
    eapply rtc_steps_thread_failure; eauto.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    exploit FAILURE; eauto. i. des.
    destruct th. destruct state0.
    hexploit sim_lift_sol_steps; eauto. i. des; eauto.
    inv FAILURE0. des. inv H. inv STEP.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    hexploit sim_lift_sol_na_local_step; eauto.
    { punfold NOMIX0. exploit NOMIX0; eauto. i. des. eapply NA; eauto.
      inv LOCAL; ss.
      { destruct ord; ss. }
      { red in ORD. destruct ordr, ordw; des; ss. }
    }
    i. des.
    { eapply rtc_steps_thread_failure; eauto.
      red. esplits; eauto. econs 2. econs; eauto.
      rewrite EVENT. eauto.
    }
    { eapply rtc_steps_thread_failure; eauto.
      red. esplits; eauto. econs 2. econs; eauto.
      rewrite EVENT. eauto.
    }
  Qed.

  Lemma sim_lift_partial_case:
    forall
      w p D smem_src smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      lang_src lang_tgt
      (st_src0: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      (LIFT: sim_state_lift w smem_src smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (PARTIAL: sim_seq_partial_case p D (SeqState.mk _ st_src0 smem_src) (SeqState.mk _ st_tgt smem_tgt))
      (BOT: lc_tgt.(Local.promises) = Memory.bot)
      (NOMIX: nomix _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step lang_src)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) \/
           (<<BOT: lc_src1.(Local.promises) = Memory.bot>>)).
  Proof.
    i. hexploit sim_lift_sim_lift_sol; eauto.
    i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    exploit PARTIAL; eauto. i.
    destruct x as [?th [?tr [?w [STEPS0 [WRITING FINAL]]]]].
    guardH FINAL. destruct th. destruct state0. des.
    hexploit sim_lift_sol_steps; eauto. i. des; eauto.
    { esplits; eauto. } esplits.
    { etrans; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    red in FINAL. des.
    { right. inv LIFT1. eapply sim_thread_none; eauto.
      i. hexploit (FLAG loc). i. inv H.
      specialize (FLAGS loc). unfold Flags.join in *.
      destruct (d loc); auto. exfalso. eapply WRITTEN; auto.
      ss. rewrite DEBT in FLAGS; auto.
      destruct (w0 loc), (flag loc), (SeqMemory.flags smem_src loc); ss.
    }
    { left. inv FAILURE. des. inv H. inv STEP.
      hexploit sim_lift_sol_na_local_step; eauto.
      { punfold NOMIX0. exploit NOMIX0; eauto. i. des. eapply NA; eauto.
        inv LOCAL; ss.
        { destruct ord; ss. }
        { red in ORD. destruct ordr, ordw; des; ss. }
      }
      i. des.
      { eapply rtc_steps_thread_failure; eauto.
        red. esplits; eauto. econs 2. econs; eauto.
        rewrite EVENT. eauto.
      }
      { eapply rtc_steps_thread_failure; eauto.
        red. esplits; eauto. econs 2. econs; eauto.
        rewrite EVENT. eauto.
      }
    }
  Qed.

  Lemma sim_lift lang_src lang_tgt sim_terminal:
    forall
      (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      w p D smem_src smem_tgt mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      (SIM: sim_seq sim_terminal p D (SeqState.mk _ st_src smem_src) (SeqState.mk _ st_tgt smem_tgt))
      (LIFT: sim_state_lift w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt),
      @sim_thread
        world world_messages_le sim_memory_lift sim_timemap_lift
        lang_src lang_tgt true w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt.
  Proof.
  Admitted.
End LIFT.