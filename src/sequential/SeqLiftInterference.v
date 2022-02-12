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

Require Import gSimulation.

Require Import JoinedView.
Require Import SeqLift.
Require Import Simple.

Require Import Pred.

Require Import SeqLiftStep.
Require Import FutureCertify.

Lemma wf_release_vers_versions_le
      vers0 vers1 prom rel_vers
      (WF: wf_release_vers vers0 prom rel_vers)
      (VERSLE: versions_le vers0 vers1)
  :
  wf_release_vers vers1 prom rel_vers.
Proof.
  inv WF. econs. i. hexploit PROM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma max_value_no_flag_le f vers srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v_src v_tgt
      (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (MAXSRC: max_value_src loc (Some v_src) mem_src lc_src)
      (MAXTGT: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF: Mapping.wfs f)
  :
    Const.le v_tgt v_src.
Proof.
  hexploit no_flag_max_value_same; eauto.
  i. des. inv MAX. inv MAXTGT.
  hexploit MAX0; eauto. i. des. hexploit MAX; eauto. i. des.
  eapply max_readable_inj in MAX1; eauto. des. subst. auto.
Qed.

Lemma max_value_sim_timestamp_exact
      f vers srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v_src v_tgt
      (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (MAXSRC: max_value_src loc (Some v_src) mem_src lc_src)
      (MAXTGT: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF: Mapping.wfs f)
  :
    sim_timestamp_exact
      (f loc) ((f loc).(Mapping.ver))
      (lc_src.(Local.tview).(TView.cur).(View.pln) loc)
      (lc_tgt.(Local.tview).(TView.cur).(View.pln) loc).
Proof.
  inv MAXTGT. hexploit MAX; eauto. i. des. inv MAX0.
  hexploit sim_memory_get; eauto; ss. i. des.
  assert (to_src = (lc_src.(Local.tview).(TView.cur).(View.pln) loc)); [|clarify].
  inv LOCAL. ss. eapply TimeFacts.antisym.
  { destruct (Time.le_lt_dec to_src (View.pln (TView.cur tvw_src) loc)); ss.
    exfalso. inv MAXSRC. hexploit MAX0; eauto. i. des. inv MAX2.
    hexploit MAX3; eauto.
    { inv MSG; ss. }
    i. hexploit sim_promises_get_if; eauto. i. des; clarify.
    hexploit sim_timestamp_exact_unique.
    { eapply TO0. }
    { eapply TO. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
    i. subst. exploit CONSISTENT; eauto.
    { inv MSG; inv MSG0; ss. }
    i. ss. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply x. }
    { eapply LOCALWF. }
  }
  { eapply sim_timestamp_le.
    { eapply TVIEW; auto. }
    { eauto. }
    { refl. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
Qed.

Variant sim_promises_past
        (reserves: list (Loc.t * Time.t * Time.t))
        (f_past: Mapping.ts)

        (srctm: Loc.t -> Time.t)
        (flag_tgt: Loc.t -> bool)
        (f: Mapping.ts)
        (vers: versions)
        (prom_src prom_tgt: Memory.t): Prop :=
| sim_promises_past_intro
    (MESSAGENORMAL: forall loc to from msg_tgt
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt))
                     (NIN: ~ List.In (loc, to, from) reserves),
        exists fto ffrom msg_src,
          (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message_max (flag_tgt loc) loc fto f (vers loc to) msg_src msg_tgt>>))
    (MESSAGERESERVE: forall loc to from msg_tgt
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt))
                     (IN: List.In (loc, to, from) reserves),
        exists fto ffrom msg_src,
          (<<FROM: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) ffrom from>>) /\
          (<<TO: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message_max (flag_tgt loc) loc fto f_past (vers loc to) msg_src msg_tgt>>) /\
          (<<RESERVE: msg_tgt = Message.reserve>>))
    (SOUND: forall loc fto ffrom msg_src
                   (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)),
        ((exists to from msg_tgt,
             (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
               (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>) /\
               (<<IN: ~ List.In (loc, to, from) reserves>>)) \/
           (exists to from msg_tgt,
               (<<TO: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) fto to>>) /\
                 (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>) /\
                 (<<IN: List.In (loc, to, from) reserves>>)) \/
           ((<<FLAG: flag_tgt loc = true>>) /\ (<<TS: Time.lt (srctm loc) fto>>) /\ (<<RESERVE: msg_src <> Message.reserve>>) /\ (<<SYNC: forall val released (MSG: msg_src = Message.concrete val (Some released)), False>>))))
    (RESERVES: forall loc from to (IN: List.In (loc, to, from) reserves),
        Memory.get loc to prom_tgt = Some (from, Message.reserve))
.

Lemma sim_promises_past_nil_sim_promises
      f_past srctm flag_tgt f vers prom_src prom_tgt
      (SIM: sim_promises_past [] f_past srctm flag_tgt f vers prom_src prom_tgt)
  :
  sim_promises srctm (fun _ => false) flag_tgt f vers prom_src prom_tgt.
Proof.
  inv SIM. econs; eauto; ss.
  i. hexploit SOUND; eauto. i. des.
  { left. esplits; eauto. }
  { ss. }
  { right. esplits; eauto. }
Qed.

Lemma promise_max_values_src
      lc0 mem0 loc from to msg lc1 mem1 kind vs
      (PROMISE: Local.promise_step lc0 mem0 loc from to msg lc1 mem1 kind)
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  inv PROMISE. ii. specialize (MAX loc0). inv MAX.
  destruct (Loc.eq_dec loc0 loc); subst.
  { econs.
    { i. hexploit MAX0; eauto. i. des. esplits. ss.
      erewrite <- promise_max_readable; eauto.
    }
    { i. hexploit NONMAX; eauto. ii. eapply H. ss.
      erewrite promise_max_readable; eauto.
    }
  }
  { eapply promise_unchanged_loc in PROMISE0; eauto. des.
    econs.
    { i. hexploit MAX0; eauto. i. des. esplits. ss.
      erewrite <- unchanged_loc_max_readable; eauto.
    }
    { i. hexploit NONMAX; eauto. ii. eapply H. ss.
      erewrite unchanged_loc_max_readable; eauto.
    }
  }
Qed.

Lemma promise_step_max_values_src
      lang st0 st1 pf e lc0 lc1 sc0 sc1 mem0 mem1 vs
      (PROMISE: Thread.promise_step pf e (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  inv PROMISE. eapply promise_max_values_src; eauto.
Qed.

Lemma promise_steps_max_values_src
      lang st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 vs
      (PROMISE: rtc (tau (@pred_step is_promise _)) (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  remember (Thread.mk lang st0 lc0 sc0 mem0).
  remember (Thread.mk lang st1 lc1 sc1 mem1).
  revert st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 Heqt Heqt0 MAX. induction PROMISE; i; clarify.
  inv H. inv TSTEP. inv STEP. inv STEP0; [|inv STEP; inv LOCAL; ss].
  destruct y. eapply promise_step_max_values_src in STEP; eauto.
Qed.

Inductive wf_reserve_list: list (Loc.t * Time.t * Time.t) -> Prop :=
| wf_reserve_list_nil
  :
  wf_reserve_list []
| wf_reserve_list_cons
    loc from to tl
    (TL: wf_reserve_list tl)
    (HD: List.Forall (fun '(loc0, to0, from0) => forall (LOC: loc0 = loc), Interval.disjoint (from, to) (from0, to0)) tl)
  :
  wf_reserve_list ((loc, to, from)::tl)
.

Lemma past_update_sim_promises
      prom_src0 loc to_tgt from_tgt reserves f_past srctm flag_tgt f vers prom_tgt
      prom_src1 prom_src2 to_src0 from_src0 to_src1 from_src1
      (SIMPROM: sim_promises_past ((loc, to_tgt, from_tgt)::reserves) f_past srctm flag_tgt f vers prom_src0 prom_tgt)
      (RESERVES: wf_reserve_list ((loc, to_tgt, from_tgt)::reserves))
      (REMOVE: Memory.remove prom_src0 loc from_src0 to_src0 Message.reserve prom_src1)
      (ADD: Memory.add prom_src1 loc from_src1 to_src1 Message.reserve prom_src2)
      (TO0: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) to_src0 to_tgt)
      (FROM0: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) from_src0 from_tgt)
      (TO1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src1 to_tgt)
      (FROM1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src1 from_tgt)
      (BOTNONE: Memory.bot_none prom_tgt)
  :
  sim_promises_past reserves f_past srctm flag_tgt f vers prom_src2 prom_tgt.
Proof.
  assert (NODUP: forall from0, ~ List.In (loc, to_tgt, from0) reserves).
  { ii. inv RESERVES. eapply List.Forall_forall in HD; eauto. ss.
    inv SIMPROM. hexploit RESERVES; eauto.
    { left. eauto. }
    i. hexploit memory_get_ts_strong; [eapply H0|]. i. des; clarify.
    { rewrite BOTNONE in H0. ss. }
    hexploit RESERVES; eauto.
    { right. eauto. }
    i. hexploit memory_get_ts_strong; [eapply H0|]. i. des; clarify.
    eapply HD; auto.
    { instantiate (1:=to_tgt). econs; ss. refl. }
    { econs; ss. refl. }
  }
  assert (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve)).
  { inv SIMPROM. eapply RESERVES0; eauto. left. auto. }
  inv SIMPROM. econs.
  { i. destruct (classic ((loc, to, from) = (loc0, to_tgt, from_tgt))).
    { clarify. esplits; eauto.
      { eapply Memory.add_get0; eauto. }
      { econs. }
    }
    { hexploit MESSAGENORMAL; eauto.
      { ii. ss. des; eauto. clarify. }
      i. des. esplits; eauto.
      eapply Memory.add_get1; eauto.
      erewrite Memory.remove_o; eauto. des_ifs.
      ss. des; clarify. exfalso.
Admitted.

Lemma sim_promises_past_update
      reserves f_past f vers flag_tgt srctm prom_tgt mem_tgt
      (MAPWF0: Mapping.wfs f_past)
      (MAPWF1: Mapping.wfs f)
      (MAPLE: Mapping.les f_past f)
      (MLETGT: Memory.le prom_tgt mem_tgt)
  :
  forall
    prom_src0 mem_src0
    (EMPTY: forall loc from0 to0 from1 to1 msg
                   (IN: List.In (loc, to0, from0) reserves)
                   (GET: Memory.get loc to1 mem_src0 = Some (from1, msg)),
        Interval.disjoint (from0, to0) (from1, to1))
    (RESERVES: wf_reserve_list reserves)
    (MLESRC: Memory.le prom_src0 mem_src0)
    (SIMMEM: sim_memory srctm (fun _ => false) f vers mem_src0 mem_tgt)
    (SIMPROM: sim_promises_past reserves f_past srctm flag_tgt f vers prom_src0 prom_tgt)
    lang st tvw sc,
  exists prom_src1 mem_src1,
    (<<STEPS: rtc (tau (@pred_step is_promise _)) (Thread.mk lang st (Local.mk tvw prom_src0) sc mem_src0) (Thread.mk lang st (Local.mk tvw prom_src1) sc mem_src1)>>) /\
      (<<SIMMEM: sim_memory srctm (fun _ => false) f vers mem_src1 mem_tgt>>) /\
      (<<SIMPROM: sim_promises srctm (fun _ => false) flag_tgt f vers prom_src1 prom_tgt>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt prom_tgt) f mem_src0 f mem_src1>>).
Proof.
  induction reserves.
  { i. esplits.
    { refl. }
    { eauto. }
    { eapply sim_promises_past_nil_sim_promises; eauto. }
    { eapply space_future_memory_refl; eauto. refl. }
  }
  i.

                                    prom_src1

.

  map_future_memory
  True.




               versioned_memory
               map_future_memory
               space_future_memory


Variant sim_promises_past
        (reserves: list (Time.t * Time.t))
        (f_past: Mapping.ts)

        (srctm: Loc.t -> Time.t)
        (flag_tgt: Loc.t -> bool)
        (f: Mapping.ts)
        (vers: versions)
        (prom_src prom_tgt: Memory.t): Prop :=


Lemma sim_thread_future
      loc_na
      f0 vers0 flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0

      f1 vers1 mem_src1 mem_tgt1 sc_src1 sc_tgt1
      lang st
      (SIM: sim_thread
              f0 vers0 (fun _ => false) flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)

      (MEMLESRC: Memory.future_weak mem_src0 mem_src1)
      (MEMLETGT: Memory.future_weak mem_tgt0 mem_tgt1)
      (CLOSEDFUTURE: closed_future_tview loc_na lc_tgt0.(Local.tview) mem_tgt0 mem_tgt1)
      (MAPFUTURE: map_future_memory f0 f1 mem_src1)
      (SPACE: space_future_memory (Messages.of_memory lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1)

      (SCLESRC: TimeMap.le sc_src0 sc_src1)
      (SCLETGT: TimeMap.le sc_tgt0 sc_tgt1)
      (SIMMEM: sim_memory_interference f1 vers1 mem_src1 mem_tgt1)
      (VERSIONED: versioned_memory vers1 mem_tgt1)
      (SIMCLOSED: sim_closed_memory f1 mem_src1)

      (SIMSC: sim_timemap (fun _ => True) f1 (Mapping.vers f1) sc_src1 sc_tgt1)
      (MAPLE: Mapping.les f0 f1)
      (VERSLE: versions_le vers0 vers1)

      (CONSISTENT: Local.promise_consistent lc_tgt0)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC0: Memory.closed mem_src0)
      (MEMTGT0: Memory.closed mem_tgt0)
      (SCSRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF0: Mapping.wfs f0)
      (VERS0: versions_wf f0 vers0)
      (MEMSRC1: Memory.closed mem_src1)
      (MEMTGT1: Memory.closed mem_tgt1)
      (SCSRC1: Memory.closed_timemap sc_src1 mem_src1)
      (SCTGT1: Memory.closed_timemap sc_tgt1 mem_tgt1)
      (WF1: Mapping.wfs f1)
      (VERS1: versions_wf f1 vers1)

      (CONSISTENTPAST: Thread.consistent (Thread.mk lang st lc_src0 sc_src0 mem_src0))
      (ATFLAG: forall loc (AT: ~ loc_na loc), flag_tgt loc = false)
  :
  exists lc_src2 sc_src2 mem_src2,
    (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk lang st lc_src0 sc_src1 mem_src1) (Thread.mk lang st lc_src2 sc_src2 mem_src2)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk lang st lc_src2 sc_src2 mem_src2)>>) \/
         exists vs_src1 vs_tgt1,
           (<<SIM: sim_thread
                     f1 vers1 (fun _ => false) flag_tgt vs_src1 vs_tgt1
                     mem_src2 mem_tgt1 lc_src2 lc_tgt0 sc_src2 sc_tgt1>>) /\
             (<<VALSRC: forall loc val (VAL: vs_src1 loc = Some val),
               exists val_old,
                 (<<VS: vs_src0 loc = Some val_old>>) /\
                   (<<VAL: Const.le val_old val>>)>>) /\
             (<<VALTGT: forall loc val (VAL: vs_tgt1 loc = Some val) (NA: loc_na loc), vs_tgt0 loc = Some val>>) /\
             (<<SPACE: space_future_memory (unchangable mem_tgt1 lc_tgt0.(Local.promises)) f1 mem_src1 f1 mem_src2>>))
.
Proof.
  destruct (classic (exists loc from0 to0 msg from1 to1,
                        (<<GET0: Memory.get loc to0 lc_src0.(Local.promises) = Some (from0, msg)>>) /\
                        (<<MSG: msg <> Message.reserve>>) /\
                        (<<GET1: Memory.get loc to1 mem_src1 = Some (from1, Message.undef)>>) /\
                        (<<TS: Time.lt to0 to1>>) /\
                        (<<NONE: Memory.get loc to1 mem_src0 = None>>))) as [|UNDEF].
  { des. hexploit FutureCertify.undef_added_failure; eauto. i. esplits; eauto. }
  assert (MEM1: sim_memory lc_src0.(Local.tview).(TView.cur).(View.rlx) (fun _ => false) f1 vers1 mem_src1 mem_tgt1).
  { eapply sim_memory_interference_sim_memory; eauto. }
  esplits; [refl|]. right.
  hexploit (@max_values_src_exists mem_src1 lc_src0).
  intros [vs_src1 MAXSRC1]. des.
  inv SIM. inv LOCAL.
  assert (VALSRC: forall loc val (VAL: vs_src1 loc = Some val),
             exists val_old,
               (<<VS: vs_src0 loc = Some val_old>>) /\
               (<<VAL: Const.le val_old val>>)).
  { i. specialize (MAXSRC loc). specialize (MAXSRC1 loc). inv MAXSRC. inv MAXSRC1.
    hexploit MAX0; eauto. i. des. destruct (vs_src0 loc) eqn:EQ.
    { hexploit MAX; eauto. i. des. inv MAX1. inv MAX2.
      eapply Memory.future_weak_get1 in GET0; eauto; ss.
      des. clarify. inv MSG_LE. esplits; eauto.
    }
    { exfalso. hexploit non_max_readable_future; eauto. }
  }
  hexploit (choice (fun loc v_tgt =>
                      (<<MAX: max_value_tgt loc v_tgt mem_tgt1 (Local.mk tvw_tgt prom_tgt)>>) /\
                      (<<OPTREL: option_rel (fun _ _ => True) (vs_src1 loc) v_tgt>>) /\
                      (<<VALTGT: forall val (VAL: v_tgt = Some val) (NA: loc_na loc), vs_tgt0 loc = Some val>>))).
  { intros loc. destruct (vs_src1 loc) eqn:VSRC.
    2:{ exists None. splits; ss. }
    hexploit VALSRC; eauto. i. des.
    specialize (MAXSRC loc). inv MAXSRC. hexploit MAX; eauto. i. des. inv MAX0.
    specialize (PERM loc). rewrite VS in PERM.
    destruct (vs_tgt0 loc) eqn:VTGT0; ss.
    specialize (MAXTGT loc). inv MAXTGT. hexploit MAX0; eauto. i. des. inv MAX2.
    specialize (MAXSRC1 loc). inv MAXSRC1. hexploit MAX2; eauto. i. des. inv MAX4.
    hexploit Memory.future_weak_get1.
    { eapply MEMLETGT. }
    { eauto. }
    { ss. }
    i. des. inv MSG_LE. exists (Some val). splits; auto.
    { econs. i. inv VAL1. esplits. econs.
      { eauto. }
      { eauto. }
      { i. hexploit sim_memory_get; ss.
        { eapply MEM1. }
        { eauto. }
        { eauto. }
        i. des. hexploit MAX5; eauto.
        { eapply sim_timestamp_lt.
          2:{ eauto. }
          { eapply sim_timestamp_mon_ver.
            { erewrite <- sim_timestamp_mon_mapping.
              { eapply TVIEW; eauto. }
              { eauto. }
              { eapply mapping_latest_wf_loc. }
              { eauto. }
            }
            { eapply MAPLE. }
            { eauto. }
            { eapply mapping_latest_wf_loc. }
          }
          { eauto. }
          { eauto. }
          { eapply mapping_latest_wf_loc. }
        }
        { inv MSG0; ss. }
        i. hexploit sim_promises_get_if; eauto. i. des.
        { admit. }
        {

        admit. }
    }
    { i. hexploit (CLOSEDFUTURE.(closed_future_cur).(closed_future_pln) loc).
      { eapply NNPP. ii. hexploit ATFLAG; eauto. }
      i. rewrite H in GET2. rewrite GET2 in GET0. inv GET0. auto.
    }
  }
  intros [vs_tgt1 MAXTGT1]. exists vs_src1, vs_tgt1. splits.
  { econs.
    { auto. }
    { eauto. }
    { econs; ss.
      { eapply sim_tview_mon_latest; eauto. }
      { econs; ss.
        { i. admit. }
        { admit. }
      }
      { eapply wf_release_vers_versions_le; eauto. }
    }
    { eauto. }
    { ii. eapply MAXTGT1. }
    { i. hexploit (MAXTGT1 loc); eauto. i. des. auto. }
    { auto. }
    { auto. }
    { auto. }
  }
  { i. hexploit VALSRC; eauto. }
  { i. hexploit (MAXTGT1 loc); eauto. i. des. eapply VALTGT; auto. }
Admitted.
