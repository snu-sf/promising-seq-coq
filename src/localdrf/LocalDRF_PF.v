Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Pred.
Require Import Trace.
Require Import JoinedView.

Require Import MemoryProps.

Require Import LocalDRFDef.

Set Implicit Arguments.


Section SEMICLOSED.

  Definition semi_closed_timemap
             (tm: TimeMap.t)
             (mem: Memory.t)
             (loc: Loc.t)
             (ts: Time.t): Prop :=
    forall l,
      (exists from val released,
          (<<GET: Memory.get l (tm l) mem = Some (from, Message.concrete val released)>>)) \/
      (<<EQ: l = loc /\ tm l = ts>>)
  .

  Lemma closed_timemap_semi_closed tm mem loc ts
        (CLOSED: Memory.closed_timemap tm mem)
    :
      semi_closed_timemap tm mem loc ts.
  Proof.
    ii. left. eauto.
  Qed.

  Lemma semi_closed_timemap_join tm0 tm1 mem loc ts
        (CLOSED0: semi_closed_timemap tm0 mem loc ts)
        (CLOSED1: semi_closed_timemap tm1 mem loc ts)
    :
      semi_closed_timemap (TimeMap.join tm0 tm1) mem loc ts.
  Proof.
    ii. specialize (CLOSED0 l). specialize (CLOSED1 l).
    unfold TimeMap.join, Time.join. des; des_ifs; eauto.
  Qed.

  Lemma semi_closed_timemap_singleton mem loc ts
        (INHABITED: Memory.inhabited mem)
    :
      semi_closed_timemap (TimeMap.singleton loc ts) mem loc ts.
  Proof.
    ii. unfold TimeMap.singleton.
    destruct (Loc.eq_dec loc l).
    - subst. right. split; auto. setoid_rewrite LocFun.add_spec_eq. auto.
    - left. esplits. setoid_rewrite LocFun.add_spec_neq; eauto.
  Qed.

  Lemma semi_closed_timemap_add tm mem0 loc from ts val released mem1
        (CLOSED: semi_closed_timemap tm mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc0). des.
    - esplits. eapply Memory.add_get1 in GET; eauto.
    - subst. eapply Memory.add_get0 in ADD. des. eauto.
  Qed.

  Lemma semi_closed_timemap_split tm mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_timemap tm mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc0). des.
    - eapply Memory.split_get1 in GET; eauto. des. eauto.
    - subst. eapply Memory.split_get0 in SPLIT. des. eauto.
  Qed.

  Lemma semi_closed_timemap_lower tm mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_timemap tm mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. specialize (CLOSED loc0). des.
    - eapply Memory.lower_get1 in GET; eauto. des. inv MSG_LE. eauto.
    - subst. eapply Memory.lower_get0 in LOWER. des. eauto.
  Qed.

  Lemma semi_closed_timemap_future tm mem0 loc ts mem1
        (CLOSED: semi_closed_timemap tm mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_timemap tm mem1 loc ts.
  Proof.
    ii. specialize (CLOSED l). des.
    - eapply Memory.future_weak_get1 in GET; eauto. des.
      inv MSG_LE. eauto.
    - subst. eauto.
  Qed.

  Inductive semi_closed_view (view:View.t) (mem:Memory.t) (loc: Loc.t) (ts: Time.t): Prop :=
  | semi_closed_view_intro
      (PLN: semi_closed_timemap view.(View.pln) mem loc ts)
      (RLX: semi_closed_timemap view.(View.rlx) mem loc ts)
  .
  Hint Constructors semi_closed_view.

  Lemma closed_view_semi_closed vw mem loc ts
        (CLOSED: Memory.closed_view vw mem)
    :
      semi_closed_view vw mem loc ts.
  Proof.
    inv CLOSED. econs.
    - eapply closed_timemap_semi_closed; eauto.
    - eapply closed_timemap_semi_closed; eauto.
  Qed.

  Lemma semi_closed_view_join vw0 vw1 mem loc ts
        (CLOSED0: semi_closed_view vw0 mem loc ts)
        (CLOSED1: semi_closed_view vw1 mem loc ts)
    :
      semi_closed_view (View.join vw0 vw1) mem loc ts.
  Proof.
    inv CLOSED0. inv CLOSED1. econs.
    - eapply semi_closed_timemap_join; eauto.
    - eapply semi_closed_timemap_join; eauto.
  Qed.

  Lemma semi_closed_view_singleton mem loc ts
        (INHABITED: Memory.inhabited mem)
    :
      semi_closed_view (View.singleton_ur loc ts) mem loc ts.
  Proof.
    econs; ss.
    - eapply semi_closed_timemap_singleton; eauto.
    - eapply semi_closed_timemap_singleton; eauto.
  Qed.

  Lemma semi_closed_view_add vw mem0 loc from ts val released mem1
        (CLOSED: semi_closed_view vw mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_add; eauto.
    - eapply semi_closed_timemap_add; eauto.
  Qed.

  Lemma semi_closed_view_split vw mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_view vw mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_split; eauto.
    - eapply semi_closed_timemap_split; eauto.
  Qed.

  Lemma semi_closed_view_lower vw mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_view vw mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_lower; eauto.
    - eapply semi_closed_timemap_lower; eauto.
  Qed.

  Lemma semi_closed_view_future vw mem0 loc ts mem1
        (CLOSED: semi_closed_view vw mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_view vw mem1 loc ts.
  Proof.
    inv CLOSED. econs.
    - eapply semi_closed_timemap_future; eauto.
    - eapply semi_closed_timemap_future; eauto.
  Qed.

  Inductive semi_closed_opt_view: forall (view:option View.t) (mem:Memory.t)
                                         (loc: Loc.t) (ts: Time.t), Prop :=
  | semi_closed_opt_view_some
      view mem loc ts
      (CLOSED: semi_closed_view view mem loc ts):
      semi_closed_opt_view (Some view) mem loc ts
  | semi_closed_opt_view_none
      mem loc ts:
      semi_closed_opt_view None mem loc ts
  .
  Hint Constructors semi_closed_opt_view.

  Lemma closed_opt_view_semi_closed vw mem loc ts
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      semi_closed_opt_view vw mem loc ts.
  Proof.
    inv CLOSED; econs.
    eapply closed_view_semi_closed; eauto.
  Qed.

  Lemma unwrap_closed_opt_view
        view mem loc ts
        (CLOSED: semi_closed_opt_view view mem loc ts)
        (INHABITED: Memory.inhabited mem):
    semi_closed_view view.(View.unwrap) mem loc ts.
  Proof.
    inv CLOSED; ss.
    eapply closed_view_semi_closed. apply Memory.closed_view_bot. ss.
  Qed.

  Lemma semi_closed_opt_view_add vw mem0 loc from ts val released mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_add; eauto.
  Qed.

  Lemma semi_closed_opt_view_split vw mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_split; eauto.
  Qed.

  Lemma semi_closed_opt_view_lower vw mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_lower; eauto.
  Qed.

  Lemma semi_closed_opt_view_future vw mem0 loc ts mem1
        (CLOSED: semi_closed_opt_view vw mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_opt_view vw mem1 loc ts.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_view_future; eauto.
  Qed.

  Inductive semi_closed_message: forall (msg:Message.t) (mem:Memory.t)
                                        (loc: Loc.t) (ts: Time.t), Prop :=
  | semi_closed_message_concrete
      val released mem loc ts
      (CLOSED: semi_closed_opt_view released mem loc ts):
      semi_closed_message (Message.concrete val released) mem loc ts
  | semi_closed_message_reserve
      mem loc ts:
      semi_closed_message Message.reserve mem loc ts
  .
  Hint Constructors semi_closed_message.

  Lemma closed_message_semi_closed msg mem loc ts
        (CLOSED: Memory.closed_message msg mem)
    :
      semi_closed_message msg mem loc ts.
  Proof.
    inv CLOSED; econs. eapply closed_opt_view_semi_closed; eauto.
  Qed.

  Lemma semi_closed_message_add vw mem0 loc from ts val released mem1
        (CLOSED: semi_closed_message vw mem0 loc ts)
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
    :
      Memory.closed_message vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_add; eauto.
  Qed.

  Lemma semi_closed_message_split vw mem0 loc ts1 ts2 ts3 msg val released mem1
        (CLOSED: semi_closed_message vw mem0 loc ts2)
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val released) msg mem1)
    :
      Memory.closed_message vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_split; eauto.
  Qed.

  Lemma semi_closed_message_lower vw mem0 loc from to msg val released mem1
        (CLOSED: semi_closed_message vw mem0 loc to)
        (LOWER: Memory.lower mem0 loc from to msg (Message.concrete val released) mem1)
    :
      Memory.closed_message vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_lower; eauto.
  Qed.

  Lemma semi_closed_message_future vw mem0 loc ts mem1
        (CLOSED: semi_closed_message vw mem0 loc ts)
        (FUTURE: Memory.future_weak mem0 mem1)
    :
      semi_closed_message vw mem1 loc ts.
  Proof.
    inv CLOSED; econs.
    eapply semi_closed_opt_view_future; eauto.
  Qed.

End SEMICLOSED.


Section SIM.

  Variable L: Loc.t -> bool.

  Inductive sim_memory_content P (loc: Loc.t)
            (* (messages: Time.t -> Prop) *)
    : option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_none
      (NPROM: ~ P)
    :
      sim_memory_content P loc None None
  | sim_memory_content_normal
      from_src from_tgt msg
      (NPROM: ~ P)
      (FROM: Time.le from_tgt from_src)
      (NLOC: ~ L loc -> from_src = from_tgt)
    :
      sim_memory_content P loc (Some (from_src, msg)) (Some (from_tgt, msg))
  | sim_memory_content_forget
      from_src from_tgt val released
      (PROM: P)
      (NLOC: L loc)
      (FROM: Time.le from_tgt from_src)
   :
      sim_memory_content P loc (Some (from_src, Message.reserve)) (Some (from_tgt, Message.concrete val released))
  .
  Hint Constructors sim_memory_content.

  Definition sim_memory P mem_src mem_tgt : Prop :=
    forall loc ts,
      sim_memory_content (P loc ts) loc (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt).

  Inductive sim_promise_content (loc: Loc.t) (ts: Time.t)
            (P: Prop)
    :
      option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_none
      (NPROM: ~ P)
    :
      sim_promise_content loc ts P None None
  | sim_promise_content_normal
      (NPROM: ~ P)
      (NLOC: ~ L loc)
      from msg
    :
      sim_promise_content loc ts P
                          (Some (from, msg))
                          (Some (from, msg))
  | sim_promise_content_normal_reserve
      (NPROM: ~ P)
      (LOC: L loc)
      (* (NLOC: ~ L loc) *)
      from_src from_tgt
    :
      sim_promise_content loc ts P
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, Message.reserve))
  | sim_promise_content_forget
      (PROM: P)
      (LOC: L loc)
      from_src from_tgt val released
    :
      sim_promise_content loc ts P
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, Message.concrete val released))
  .
  Hint Constructors sim_promise_content.

  Definition sim_promise
             (self: Loc.t -> Time.t -> Prop)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content loc ts (self loc ts)
                          (Memory.get loc ts prom_src)
                          (Memory.get loc ts prom_tgt).

  Inductive sim_local (self: Loc.t -> Time.t -> Prop)
    :
      forall (lc_src lc_tgt: Local.t), Prop :=
  | sim_local_intro
      tvw prom_src prom_tgt
      (PROMS: sim_promise self prom_src prom_tgt)
    :
      sim_local self (Local.mk tvw prom_src) (Local.mk tvw prom_tgt)
  .
  Hint Constructors sim_local.

  Inductive sim_statelocal (self: Loc.t -> Time.t -> Prop):
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc_src lc_tgt
      (LOCAL: sim_local self lc_src lc_tgt)
    :
      sim_statelocal self (st, lc_src) (st, lc_tgt)
  .

  Inductive all_promises (proms: Ident.t -> Loc.t -> Time.t -> Prop): Loc.t -> Time.t -> Prop :=
  | all_promises_intro
      tid loc ts
      (PROMS: proms tid loc ts)
    :
      all_promises proms loc ts
  .
  Hint Constructors all_promises.

  Lemma sim_read_step P self lc_src lc_tgt mem_src mem_tgt loc to val released ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released ord lc_tgt')
        (NOREAD: ~ P loc to)
        (MEM: sim_memory P mem_src mem_tgt)
        (LOCAL: sim_local self lc_src lc_tgt)
    :
      exists lc_src' released,
        (<<STEPSRC: Local.read_step lc_src mem_src loc to val released ord lc_src'>>) /\
        (<<SIM: sim_local self lc_src' lc_tgt'>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_src = Some (from, Message.concrete val released)>>) /\
        (<<GETTGT: exists from, Memory.get loc to mem_tgt = Some (from, Message.concrete val released)>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    specialize (MEM loc to). rewrite GET in *. inv MEM; ss.
    esplits; eauto.
  Qed.

  Lemma sim_fence_step self lc_src lc_tgt sc ordr ordw
        sc' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc ordr ordw lc_tgt' sc')
        (LOCAL: sim_local self lc_src lc_tgt)
    :
      exists lc_src',
        (<<STEPSRC: Local.fence_step lc_src sc ordr ordw lc_src' sc'>>) /\
        (<<SIM: sim_local self lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT. esplits.
    - econs; ss; eauto. ii.
      specialize (PROMS loc t). rewrite GET in *. inv PROMS; ss.
      exploit RELEASE; eauto.
    - econs; ss; eauto.
  Qed.

  Lemma sim_promise_consistent prom_self lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local prom_self lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii. ss.
    specialize (PROMS loc ts). rewrite PROMISE in *. inv PROMS. eauto.
  Qed.

  Lemma sim_failure_step prom_self lc_src lc_tgt
        (STEPTGT: Local.failure_step lc_tgt)
        (SIM: sim_local prom_self lc_src lc_tgt)
    :
      Local.failure_step lc_src.
  Proof.
    inv STEPTGT. econs.
    eapply sim_promise_consistent; eauto.
  Qed.

  Lemma sim_memory_others_self_wf
        P mem_src mem_tgt
        (MEMORY: sim_memory P mem_src mem_tgt)
    :
      forall loc' to', P loc' to' -> L loc'.
  Proof.
    ii. specialize (MEMORY loc' to'). inv MEMORY; clarify.
  Qed.

  Lemma sim_promise_step_normal others self mem_src mem_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt' kind
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (SEMI: semi_closed_message msg mem_src loc to)
    :
      exists prom_src' mem_src',
        (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' kind>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self prom_src' prom_tgt'>>) /\
        (<<PROMATTACH: promises_not_attached self (promised prom_src') mem_src'>>) /\
        (<<CLOSED: Memory.closed_message msg mem_src'>>)
  .
  Proof.
    generalize (sim_memory_others_self_wf MEM). intros PROMSWF.
    inv STEPTGT.

    (* add case *)
    - exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg); ss.
      { i. specialize (MEM loc to2). rewrite GET2 in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (ATTACHSRC: forall val released to' msg'
                                (MSG: msg = Message.concrete val released)
                                (GET: Memory.get loc to' mem_src = Some (to, msg')), False).
      { i. clarify.
        specialize (MEM loc to'). rewrite GET in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; eauto. }
        inv FROM.
        { exploit DISJOINT; auto.
          - symmetry. eapply H.
          - instantiate (1:=to). econs; ss. refl.
          - econs; ss. eapply memory_get_ts_le; eauto.
        }
        { inv H0. exploit ATTACH; eauto. }
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg mem_src').
      { destruct msg; auto.
        eapply semi_closed_message_add; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * econs; eauto.
          { ii. ss. des; clarify; eauto. }
          { refl. }
      + ii. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso. eauto.
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. destruct msg; econs; eauto.
      + ii. erewrite promised_add; eauto.
        erewrite (@Memory.add_o mem_src' mem_src) in GET; eauto.
        des_ifs; try by (des; ss; clarify).
        { ss. des; clarify. exfalso. eauto. }
        { eapply PROMATTACH; eauto. }

    (* split case *)
    - exploit split_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc ts3). rewrite GET2 in *.
      inv PROMISE0; ss.

      hexploit (@Memory.split_exists prom_src loc from to ts3 (Message.concrete val' released')); ss.
      { eauto. }
      intros [prom_src' SPLITPROMSRC].
      exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
      intros [mem_src' SPLITMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val' released') prom_src' mem_src' (Memory.op_kind_split ts3 msg3)).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message (Message.concrete val' released') mem_src').
      { eapply semi_closed_message_split; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.split_o mem_src'); eauto.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        { ss. des; clarify. econs; eauto.
          * refl. }
        { guardH o. ss. des; clarify. econs; eauto.
          * refl. }
      + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
        * ss. des; clarify. exfalso. eauto.
        * guardH o. ss. des; clarify. exfalso. eauto.
      + ii. erewrite (@Memory.split_o prom_src'); eauto.
        erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * guardH o. ss. des; clarify. econs; eauto.
      + ii. erewrite promised_split; eauto.
        erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto.
        des_ifs; try by (des; ss; clarify).
        * ss. des; clarify. exfalso. eauto.
        * guardH o. ss. des; clarify. exfalso. eauto.
        * eapply PROMATTACH; eauto.

    (* lower case *)
    - exploit lower_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *. inv PROMISE0; ss.

      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released) msg); ss.

      intros [prom_src' LOWERPROMSRC].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val released))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg mem_src').
      { destruct msg; auto.
        eapply semi_closed_message_lower; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_src'); eauto.
        erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * refl.
      + ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso. eauto.
      + ii. erewrite (@Memory.lower_o prom_src'); eauto.
        erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
      + ii. erewrite promised_lower; eauto.
        erewrite Memory.lower_o in GET0; eauto.
        des_ifs; try by (des; ss; clarify).
        * ss. des; clarify. exfalso; eauto.
        * eapply PROMATTACH; eauto.

    (* cancel case *)
    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; ss.

      hexploit (@Memory.remove_exists prom_src loc from to Message.reserve); ss.
      intros [prom_src' REMOVEPROMSRC].
      exploit Memory.remove_exists_le; try apply REMOVEPROMSRC; eauto.
      intros [mem_src' REMOVEMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists prom_src', mem_src'.
      splits; auto.
      + ii. erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto.
        des_ifs; try by (des; ss; clarify).
        * ss. des; clarify. econs; eauto.
      + ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs; eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs. ii. eauto.
      + ii. erewrite promised_remove; eauto.
        erewrite (@Memory.remove_o mem_src') in GET1; eauto.
        des_ifs; try by (des; ss; clarify).
        * eapply PROMATTACH; eauto.
        * eapply PROMATTACH; eauto.
  Qed.

  Lemma sim_write_step_normal
        others self lc_src lc_tgt sc mem_src mem_tgt
        lc_tgt' sc' mem_tgt' loc from to val ord releasedm released kind
        (NLOC: ~ L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self lc_src lc_tgt)
        (PROMATTACH: promises_not_attached self (promised lc_src.(Local.promises)) mem_src)
        (CONSISTENT: Local.promise_consistent lc_tgt')

        (RELEASEDMCLOSED: Memory.closed_opt_view releasedm mem_src)
        (RELEASEDMWF: View.opt_wf releasedm)
    :
      exists lc_src' mem_src',
        (<<STEPSRC: Local.write_step lc_src sc mem_src loc from to val releasedm released ord lc_src' sc' mem_src' kind>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SIM: sim_local self lc_src' lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv WRITE. inv SIM. inv LOCALSRC. inv LOCALTGT.

    hexploit sim_promise_step_normal; eauto.
    { ss. econs. unfold TView.write_released. des_ifs; econs.
      eapply semi_closed_view_join.
      - inv MEMSRC. eapply unwrap_closed_opt_view; auto.
        eapply closed_opt_view_semi_closed. auto.
      - ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. inv TVIEW_CLOSED. auto.
          * inv MEMSRC. eapply semi_closed_view_singleton. auto.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. inv TVIEW_CLOSED. auto.
          * inv MEMSRC. eapply semi_closed_view_singleton. auto.
    }
    i. des. ss.

    hexploit (@Memory.remove_exists
                prom_src' loc from to
                (Message.concrete val (TView.write_released tvw sc loc to releasedm ord))).
    { specialize (PROMISE0 loc to).
      eapply Memory.remove_get0 in REMOVE. des.
      rewrite GET in *. inv PROMISE0; ss. }
    intros [prom_src'' REMOVESRC].

    assert (NSELF: forall ts, ~ self loc ts).
    { ii. specialize (PROMISE0 loc ts). inv PROMISE0; ss. }

    esplits; eauto.

    - econs; ss.
      + econs; eauto.
      + ii. specialize (PROMS loc t).
        rewrite GET in *. inv PROMS; ss.
        exploit RELEASE; eauto.
    - ss. ii. exploit PROMATTACH0; eauto. i.
      erewrite promised_remove; eauto. des_ifs. eapply NSELF; eauto.

    - econs; auto. ii.
      erewrite (@Memory.remove_o prom_src''); eauto.
      erewrite (@Memory.remove_o promises2); eauto. des_ifs.
      ss. des; subst. econs; eauto.
  Qed.

  Inductive sim_promise_content_strong (loc: Loc.t) (ts: Time.t)
            (P: Prop) (messages: Time.t -> Prop)
    :
      option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_strong_none
      (NPROM: ~ P)
    :
      sim_promise_content_strong loc ts P messages None None
  | sim_promise_content_strong_normal_concrete
      (NPROM: ~ P)
      (NLOC: ~ L loc)
      from msg
    :
      sim_promise_content_strong loc ts P messages
                                 (Some (from, msg))
                                 (Some (from, msg))
  | sim_promise_content_strong_normal_reserve
      (NPROM: ~ P)
      (LOC: L loc)
      from_src from_tgt
      (NOTHERS: forall (LOC: L loc) (MSG: messages from_tgt), from_tgt = from_src)
    :
      sim_promise_content_strong loc ts P messages
                                 (Some (from_src, Message.reserve))
                                 (Some (from_tgt, Message.reserve))
  | sim_promise_content_strong_forget
      (PROM: P)
      (LOC: L loc)
      from_src from_tgt val released
      (NOTHERS: forall (MSG: messages from_tgt), from_tgt = from_src)
    :
      sim_promise_content_strong loc ts P messages
                                 (Some (from_src, Message.reserve))
                                 (Some (from_tgt, Message.concrete val released))
  .
  Hint Constructors sim_promise_content_strong.

  Lemma sim_promise_content_strong_sim_promise_content
        loc ts P get0 get1 messages
        (SIM: sim_promise_content_strong loc ts P messages get0 get1)
    :
      sim_promise_content loc ts P get0 get1.
  Proof.
    inv SIM; econs; eauto.
  Qed.

  Definition sim_promise_strong
             (self messages: Loc.t -> Time.t -> Prop)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content_strong loc ts (self loc ts)
                                 (messages loc)
                                 (Memory.get loc ts prom_src)
                                 (Memory.get loc ts prom_tgt).

  Lemma sim_promise_strong_sim_promise
        self messages prom_src prom_tgt
        (SIM: sim_promise_strong self messages prom_src prom_tgt)
    :
      sim_promise self prom_src prom_tgt.
  Proof.
    ii. eapply sim_promise_content_strong_sim_promise_content; eauto.
  Qed.

  Definition sim_promise_list (self messages: Loc.t -> Time.t -> Prop)
             (prom_src prom_tgt: Memory.t)
             (l: list (Loc.t * Time.t)): Prop :=
    forall loc ts,
      (<<NORMAL: sim_promise_content_strong loc ts (self loc ts) (messages loc)
                                            (Memory.get loc ts prom_src)
                                            (Memory.get loc ts prom_tgt)>>) \/
      ((<<LIN: List.In (loc, ts) l>>) /\
       (<<WEAK: sim_promise_content loc ts (self loc ts)
                                    (Memory.get loc ts prom_src)
                                    (Memory.get loc ts prom_tgt)>>)).

  Lemma sim_promise_list_nil self messages prom_src prom_tgt
        (SIM: sim_promise_list self messages prom_src prom_tgt [])
    :
      sim_promise_strong self messages prom_src prom_tgt.
  Proof.
    ii. exploit SIM; eauto. i. des; eauto. ss.
  Qed.

  Lemma sim_promise_weak_list_exists self messages prom_src prom_tgt
        (SIM: sim_promise self prom_src prom_tgt)
        (FIN: Memory.finite prom_src)
    :
      exists l,
        (<<SIM: sim_promise_list self messages prom_src prom_tgt l>>).
  Proof.
    unfold Memory.finite in *. des.
    hexploit (@list_filter_exists
                (Loc.t * Time.t)
                (fun locts =>
                   let (loc, ts) := locts in
                   ~ sim_promise_content_strong loc ts (self loc ts) (messages loc)
                     (Memory.get loc ts prom_src)
                     (Memory.get loc ts prom_tgt))
                dom).
    i. des. exists l'.
    ii. destruct (classic (List.In (loc,ts) l')).
    - right. splits; auto.
    - left. specialize (SIM loc ts). red. inv SIM; try by (econs; eauto).
      + apply NNPP. ii. exploit FIN; eauto. i.
        hexploit (proj1 (@COMPLETE (loc, ts))); auto.
        splits; auto. ii. rewrite H1 in *. rewrite H2 in *. auto.
      + apply NNPP. ii. exploit FIN; eauto. i.
        hexploit (proj1 (@COMPLETE (loc, ts))); auto.
        splits; auto. ii. rewrite H1 in *. rewrite H2 in *. auto.
  Qed.

  Lemma promises_not_attached_replaces self loc ts prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (* (SELF: self <2= promised prom0) *)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot ts)
        (* (SELF: self loc ts) *)
        (PROMISED: promised prom0 loc ts)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<UNCH01: forall loc' to (TS: loc' = loc -> Time.le to ts),
            (<<MEM: Memory.get loc' to mem1 = Memory.get loc' to mem0>>) /\
            (<<PROM: Memory.get loc' to prom1 = Memory.get loc' to prom0>>)>>) /\

        (<<ATTACH: forall to msg (SELF: self loc ts) (GET: Memory.get loc to mem1 = Some (ts, msg)), False>>) /\
        (* (<<ATTACH: forall to msg (GET: Memory.get loc to mem1 = Some (ts, msg)), False>>) /\ *)

        (<<MLE1: Memory.le prom1 mem1>>) /\

        (<<RESTORE:
           forall prom2 mem2
                  (UNCH12: forall loc' to (TS: loc' = loc -> Time.lt ts to),
                      (<<MEM: Memory.get loc' to mem2 = Memory.get loc' to mem1>>) /\
                      (<<PROM: Memory.get loc' to prom2 = Memory.get loc' to prom1>>))
                  (MLE2: Memory.le prom2 mem2)
           ,
           exists prom3 mem3,
             (<<FUTURE23: reserve_future_memory prom2 mem2 prom3 mem3>>) /\
             (<<UNCHANGED: forall loc' to (TS: loc' = loc -> Time.lt ts to),
                 (<<MEM: Memory.get loc' to mem3 = Memory.get loc' to mem0>>) /\
                 (<<PROM: Memory.get loc' to prom3 = Memory.get loc' to prom0>>)>>) /\
             (<<CHANGED: forall to (TS: Time.le to ts),
                 (<<MEM: Memory.get loc to mem3 = Memory.get loc to mem2>>) /\
                 (<<PROM: Memory.get loc to prom3 = Memory.get loc to prom2>>)>>) /\
             (<<MLE3: Memory.le prom3 mem3>>)
               >>).
  Proof.
    destruct (classic (self loc ts)) as [SELF|NSELF]; cycle 1.
    { exists prom0, mem0. splits; eauto. i. esplits; eauto. }
    destruct (classic (exists to msg, <<GET: Memory.get loc to mem0 = Some (ts, msg)>>)); cycle 1.
    { exists prom0, mem0. splits; eauto. i. esplits; eauto. }
    des. exploit ATTACHED; eauto. i. inv x. destruct msg0 as [from msg0].
    dup GET0. apply MLE0 in GET1. clarify.
    exploit LOC; eauto. i. clarify.

    assert (TSTO: Time.lt ts to).
    { eapply memory_get_ts_strong in GET0. des; auto. clarify. }

    exploit Memory.remove_exists.
    { eapply GET0. }
    intros [prom1 REMOVEPROM].
    exploit Memory.remove_exists_le; eauto.
    intros [mem1 REMOVEMEM].

    assert (REMOVE: Memory.promise prom0 mem0 loc ts to Message.reserve prom1 mem1 Memory.op_kind_cancel).
    { econs; eauto. }
    exists prom1, mem1. splits; eauto.
    { i. erewrite (@Memory.remove_o mem1); eauto.
      erewrite (@Memory.remove_o prom1); eauto. des_ifs.
      ss. des; clarify.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    }
    { i. erewrite Memory.remove_o in GET; eauto. des_ifs. ss. des; clarify.
      exploit memory_get_from_inj.
      { eapply GET. }
      { eapply GET1. }
      i. des; clarify.
      { eapply Time.lt_strorder; eauto. }
      { eapply Time.lt_strorder; eauto. }
    }
    { eapply promise_memory_le; eauto. }
    { i. hexploit (@Memory.add_exists mem2 loc ts to Message.reserve).
      { ii. hexploit (@UNCH12 loc to2).
        { i. inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
        i. des. rewrite H in *.
        erewrite (@Memory.remove_o mem1) in GET2; eauto. des_ifs. guardH o.
        exploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply GET1. }
        i. des; clarify.
        - ss. unguard. des; clarify.
        - eapply x1; eauto.
      }
      { auto. }
      { econs. }
      intros [mem3 ADDMEM].
      hexploit (Memory.add_exists_le); eauto.
      intros [prom3 ADDPROM].

      assert (ADD: Memory.promise prom2 mem2 loc ts to Message.reserve prom3 mem3 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      exists prom3, mem3. splits; auto.
      { eapply reserve_future_memory_trans; eauto. }

      { i. exploit UNCH12; eauto. i. des.
        erewrite (@Memory.add_o mem3); eauto.
        erewrite (@Memory.add_o prom3); eauto.
        erewrite x. erewrite x0.
        erewrite (@Memory.remove_o mem1); eauto.
        erewrite (@Memory.remove_o prom1); eauto. des_ifs.
        ss. des; clarify. }
      { i. erewrite (@Memory.add_o mem3); eauto.
        erewrite (@Memory.add_o prom3); eauto. des_ifs.
        ss. des; clarify.
        exfalso. eapply Time.lt_strorder.
        eapply (@TimeFacts.le_lt_lt to ts); eauto. }
      { eapply promise_memory_le; eauto. }
    }
  Qed.

  Lemma promises_not_attached_replace_add self loc from from' to prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (* (PROMISED: self loc to) *)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem1 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.reserve)
            else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom1 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.reserve)
            else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    { econs; eauto. }
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit (@Memory.add_exists mem2 loc from' to Message.reserve); eauto.

    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }
    { econs. }
    intros [mem2' ADDMEM].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to Message.reserve); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM].
    assert (PROMISE1: Memory.promise prom2 mem2 loc from' to Message.reserve prom2' mem2' Memory.op_kind_add).
    { econs; eauto. i. clarify. }
    hexploit (@RESTORE prom2' mem2'); eauto.
    { i. erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.add_o prom2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des. exists prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.add_o prom2' prom2); eauto.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
  Qed.

  Lemma sim_promise_weak_stengthen others self prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONE: Memory.bot_none prom_src)
        (PROM: sim_promise self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (* (SELF: self <2= promised prom_src) *)
        (EXCLUSIVE: forall loc' ts' (SELF: self loc' ts') (OTHER: others loc' ts'), False)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self (promised prom_src') mem_src'>>) /\
        (<<PROM: sim_promise_strong
                   self (concrete_promised mem_src' \2/ self)
                   (* (fun loc' ts' => concrete_promise *)
                   (*    concrete_promised prom_src' loc' ts' /\ *)
                   (*    ~ others loc' ts' *)
                   (* ) *)
                   prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      - refl.
      - eapply sim_promise_list_nil; eauto. }
    i. destruct a as [loc ts].
    dup SIM. specialize (SIM0 loc ts). des.
    { exploit IHl; eauto. ii.
      destruct (loc_ts_eq_dec (loc0, ts0) (loc, ts)).
      - ss. des; clarify. left. auto.
      - specialize (SIM loc0 ts0). ss. des; auto; clarify. }

    clear LIN.

    destruct (Memory.get loc ts prom_src) as [[from_src [val released|]]|] eqn:GETSRC; cycle 2.
    { inv WEAK. exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H. rewrite GETSRC. econs; eauto. }
    { inv WEAK. exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H. rewrite GETSRC. econs; eauto. }
    assert (exists from_tgt msg, <<GETTGT: Memory.get loc ts prom_tgt = Some (from_tgt, msg)>>).
    { inv WEAK; eauto. } des. rewrite GETTGT in *.

    destruct (classic ((concrete_promised mem_src \2/ self) loc from_tgt)) as [OTHER|NOTHER]; cycle 1.
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite GETTGT. rewrite GETSRC. inv WEAK.
      - econs 2; eauto.
      - econs 3; eauto. clarify.
      - econs 4; eauto. clarify. }
    guardH OTHER.

    assert (NBOT: Time.lt Time.bot ts).
    { destruct (Time.le_lt_dec ts Time.bot); auto. destruct l0.
      - exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      - inv H. erewrite BOTNONE in GETSRC. clarify. }

    destruct (classic (L loc)) as [LOC|NLOC]; cycle 1.
    { hexploit (@IHl others self prom_src prom_tgt mem_src mem_tgt); eauto.
      ii. specialize (SIM loc0 ts0). ss. des; eauto. clarify.
      left. inv WEAK; eauto.
      - rewrite GETSRC. rewrite GETTGT. econs 2; eauto.
      - rewrite GETSRC. rewrite GETTGT. econs 3; eauto. i. clarify.
      - rewrite GETSRC. rewrite GETTGT. econs 4; eauto. i. clarify. }

    exploit promises_not_attached_replace_add.
    { eauto. }
    { eauto. }
    { ii. specialize (SIM loc to). rewrite GET in *. des.
      - inv NORMAL; eauto; try by (exfalso; eauto).
      - inv WEAK0; eauto; try by (exfalso; eauto). }
    { eauto. }
    { eauto. }
    { eauto. }
    { instantiate (1:=from_tgt).
      apply memory_get_ts_strong in GETTGT. des; clarify. }
    { ii. inv H. specialize (MEM loc to). rewrite GET in MEM.
      inv MEM; clarify.
      - exploit Memory.get_disjoint.
        { symmetry. apply H. }
        { eapply MLETGT. eapply GETTGT. }
        i. des; clarify.
        + eapply MLESRC in GETSRC. clarify.
          inv ITV. inv ITV0. ss. clear - TO FROM1.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + eapply x0.
          * instantiate (1:=ts0). econs; ss.
            { inv ITV0. eapply TimeFacts.le_lt_lt; eauto. }
            { inv ITV0. ss. }
          * inv ITV. econs; ss. etrans; eauto.
            eapply memory_get_ts_le; eauto.
      - guardH PROM. exploit Memory.get_disjoint.
        { symmetry. apply H. }
        { eapply MLETGT. eapply GETTGT. }
        i. des; clarify.
        + eapply MLESRC in GETSRC. clarify.
          inv ITV. inv ITV0. ss. clear - TO FROM1.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + eapply x0.
          * instantiate (1:=ts0). econs; ss.
            { inv ITV0. eapply TimeFacts.le_lt_lt; eauto. }
            { inv ITV0. ss. }
          * inv ITV. econs; ss. etrans; eauto.
            eapply memory_get_ts_le; eauto.
    }
    i. des.
    assert (PROMISEDSAME: promised prom1 = promised prom_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite PROMSPEC in GET. des_ifs.
        + ss. des; clarify. econs; eauto.
        + econs; eauto.
      - inv H. specialize (PROMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. econs; eauto.
        + erewrite <- PROMSPEC in *. econs; eauto. }
    assert (CONCRETESAME: concrete_promised mem1 = concrete_promised mem_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite MEMSPEC in GET. des_ifs. econs; eauto.
      - inv H. specialize (MEMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. apply MLESRC in GETSRC. clarify.
        + erewrite <- MEMSPEC in *. econs; eauto. }

    assert (PROMISEDSAMEMEM: promised mem1 = promised mem_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite MEMSPEC in GET. des_ifs.
        + ss. des; clarify. econs; eauto.
        + econs; eauto.
      - inv H. specialize (MEMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. econs; eauto.
        + erewrite <- MEMSPEC in *. econs; eauto. }

    hexploit (@IHl others self prom1 prom_tgt mem1 mem_tgt); eauto.
    { ii.
      dup MEM. specialize (MEM0 loc0 ts0). erewrite MEMSPEC. des_ifs.
      - ss. des; clarify. apply MLETGT in GETTGT. rewrite GETTGT.
        rewrite GETTGT in *. apply MLESRC in GETSRC. rewrite GETSRC in *.
        inv MEM0; eauto.
        + econs 2; eauto. refl.
        + econs 3; eauto. refl.
    }
    { eapply reserve_future_memory_le; eauto. }
    { eapply reserve_future_memory_finite; eauto. }
    { eapply reserve_future_memory_bot_none; eauto. }
    { ii. rewrite MEMSPEC in GET.
      erewrite PROMISEDSAME. des_ifs.
      - ss. des; clarify. econs; eauto.
      - exploit PROMATTACH; eauto. }
    { ii. erewrite PROMSPEC. des_ifs.
      - left. ss. des. clarify. erewrite GETTGT. inv WEAK; eauto.
      - guardH o. specialize (SIM loc0 ts0).
        ss. rewrite CONCRETESAME. des; eauto.
        unguard. des; clarify. }
    i. des. exists prom_src', mem_src'. splits; auto.
    - eapply reserve_future_memory_trans; eauto.
    - etrans; eauto. ii.
      erewrite MEMSPEC in GET. des_ifs.
      + ss. des; clarify. exfalso.
        specialize (MEM loc from). unguard. des.
        * inv OTHER. erewrite GET in MEM. inv MEM. eauto.
        * eauto.
      + eauto.
  Qed.

  Lemma promises_not_attached_replace_write self loc from from' to prom0 mem0 val released
        (LIN: L loc)
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (* (SELF: self <2= promised prom0) *)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (PROMISED: self loc to)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
        (VIEWWF: View.opt_wf released)
        (MSGTO: Time.le (View.rlx (View.unwrap released) loc) to)
    :
      exists prom1 mem1 prom2 mem2 prom3 mem3,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<WRITE: Memory.write prom1 mem1 loc from' to val released prom2 mem2 Memory.op_kind_add>>) /\
        (<<FUTURE23: reserve_future_memory prom2 mem2 prom3 mem3>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem3 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.concrete val released)
            else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom3 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then None
            else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    { econs; eauto. }
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit (@Memory.add_exists mem2 loc from' to (Message.concrete val released)); eauto.

    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }
    { econs; eauto. }
    intros [mem2' ADDMEM].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to (Message.concrete val released)); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM].

    assert (PROMISE1: Memory.write prom2 mem2 loc from' to val released prom2 mem2' Memory.op_kind_add).
    { econs; eauto.
      - econs; eauto. i.
        erewrite (@Memory.remove_o mem2) in GET0; eauto.
        des_ifs. eauto.
      - exploit Memory.remove_exists.
        { eapply Memory.add_get0 in ADDPROM. des. eapply GET1. }
        i. des.
        exploit MemoryFacts.add_remove_eq; eauto. i. subst. auto.
    }

    hexploit (@RESTORE prom2 mem2'); eauto.
    { i. erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
    { eapply write_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des.
    exists prom2, mem2, prom2, mem2', prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
  Qed.


  Lemma promises_not_attached_replace_split self loc from from' to' to prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (* (SELF: self <2= promised prom0) *)
        (* (PROMISED: self loc to) *)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to')
        (TO: Time.lt to' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem1 =
            if loc_ts_eq_dec (loc', ts') (loc, to')
            then Some (from', Message.reserve)
            else if loc_ts_eq_dec (loc', ts') (loc, to)
                 then Some (to', Message.reserve)
                 else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom1 =
            if loc_ts_eq_dec (loc', ts') (loc, to')
            then Some (from', Message.reserve)
            else if loc_ts_eq_dec (loc', ts') (loc, to)
                 then Some (to', Message.reserve)
                 else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    { econs; eauto. }
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    assert (DISJOINT: forall (to2 from2 : Time.t) (msg2 : Message.t)
                             (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
               Interval.disjoint (from', to) (from2, to2)).
    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }

    hexploit (@Memory.add_exists mem2 loc from' to' Message.reserve); eauto.
    { ii. eapply DISJOINT; eauto. inv LHS. econs; ss.
      etrans; eauto. left. auto. }
    { econs. }
    intros [mem2' ADDMEM0].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to' Message.reserve); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM0].
    assert (PROMISE1: Memory.promise prom2 mem2 loc from' to' Message.reserve prom2' mem2' Memory.op_kind_add).
    { econs; eauto. i. clarify. }

    hexploit (@Memory.add_exists mem2' loc to' to Message.reserve); eauto.
    { ii. erewrite Memory.add_o in GET2; eauto. des_ifs.
      - ss. des; clarify. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
      - guardH o. eapply DISJOINT; eauto. inv LHS. econs; ss.
        etrans; eauto. }
    { econs. }
    intros [mem2'' ADDMEM1].
    hexploit (@Memory.add_exists_le prom2' mem2' loc to' to Message.reserve); eauto.
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    intros [prom2'' ADDPROM1].

    assert (PROMISE2: Memory.promise prom2' mem2' loc to' to Message.reserve prom2'' mem2'' Memory.op_kind_add).
    { econs; eauto. i. clarify. }
    hexploit (@RESTORE prom2'' mem2''); eauto.
    { i. erewrite (@Memory.add_o mem2''); eauto.
      erewrite (@Memory.add_o prom2''); eauto.
      erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.add_o prom2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      - ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - guardH o. ss. des; clarify. exfalso.
        eapply Time.lt_strorder. etrans; eauto.
    }
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des. exists prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2'' mem2'); eauto.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs.
        + ss. des; clarify.
        + guardH o. guardH o0. hexploit (@UNCH01 loc ts'); eauto.
          { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
          i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.add_o prom2'' prom2'); eauto.
        erewrite (@Memory.add_o prom2' prom2); eauto.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs.
        + ss. des; clarify.
        + guardH o. hexploit (@UNCH01 loc ts'); eauto.
          { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
          i. des; clarify.
    }
  Qed.


  Lemma sim_promise_step_forget others self pasts mem_src mem_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (LOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (EXCLUSIVE: forall loc' ts' (SELF: promised prom_src loc' ts') (OTHER: others loc' ts'), False)
    :
      exists prom_src' mem_src' self',
        (<<STEPSRC: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self' prom_src' prom_tgt'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised prom_src') mem_src'>>)
  .
  Proof.
    inv STEPTGT.

    - hexploit add_succeed_wf; try apply MEM0. i. des.

      assert (DISJOINTSRC:
                forall to2 from2 msg2
                       (GET2: Memory.get loc to2 mem_src = Some (from2, msg2)),
                  Interval.disjoint (Time.middle from to, to) (from2, to2)).
      { ii. specialize (MEM loc to2). inv MEM.
        - rewrite GET2 in *. clarify.
        - rewrite GET2 in *. clarify. eapply DISJOINT; eauto.
          + instantiate (1:=x). inv LHS. econs; ss.
            transitivity (Time.middle from to); auto.
            eapply Time.middle_spec; auto.
          + inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto.
        - rewrite GET2 in *. clarify. eapply DISJOINT; eauto.
          + instantiate (1:=x). inv LHS. econs; ss.
            transitivity (Time.middle from to); auto.
            eapply Time.middle_spec; auto.
          + inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      hexploit (@Memory.add_exists mem_src loc (Time.middle from to) to Message.reserve).
      { auto. }
      { eapply Time.middle_spec; auto. }
      { econs. }
      intros [mem_src' ADDMEM].
      hexploit (@Memory.add_exists_le prom_src mem_src loc (Time.middle from to) to Message.reserve); eauto.
      intros [prom_src' ADDPROM].
      assert (PROMISESRC: Memory.promise prom_src mem_src loc (Time.middle from to) to Message.reserve prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. i. clarify. }
      assert (FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src').
      { eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then msg_tgt <> Message.reserve else self loc' ts').
      splits; auto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. destruct msg_tgt.
          { econs 3; eauto.
            - right. clarify.
            - left. eapply Time.middle_spec; eauto. }
          { econs 2; eauto.
            - ii. des; eauto. exfalso.
              specialize (MEM loc to). eapply Memory.add_get0 in ADDMEM.
              des. rewrite GET in *. inv MEM. eauto.
            - left. eapply Time.middle_spec; eauto.
            - i. clarify.
          }
      + ii. erewrite Memory.add_o in GET; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso.
        specialize (MEM loc (Time.middle from to)). inv MEM.
        { eapply NPROM; auto. }
        { eapply NPROM; auto. }
        { guardH PROM. exploit Memory.get_disjoint.
          { eapply Memory.add_get1; try apply MEM0. symmetry. eapply H. }
          { eapply Memory.add_get0; eauto. }
          i. des.
          - subst. eapply Time.lt_strorder.
            instantiate (1:=to). rewrite <- x0 at 1.
            eapply Time.middle_spec. auto.
          - eapply x0.
            + instantiate (1:=Time.middle from to). econs; ss.
              * symmetry in H. eapply memory_get_ts_strong in H. des; auto.
                subst. eapply TimeFacts.le_lt_lt.
                { eapply Time.bot_spec. }
                { eapply Time.middle_spec in TO1. des. eauto. }
              * refl.
            + econs; ss.
              * eapply Time.middle_spec; eauto.
              * left. eapply Time.middle_spec; eauto.
        }
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. destruct msg_tgt.
        * econs 4; eauto. clarify.
        * econs 3; eauto.
      + ii. erewrite promised_add; eauto.
        erewrite Memory.add_o in GET; eauto.
        destruct msg_tgt; cycle 1.
        { des_ifs; eauto; try by (ss; des; clarify). }
        des_ifs; eauto; ss; des; clarify.
        specialize (MEM loc ts1). rewrite GET in *. inv MEM.
        { exfalso. destruct FROM.
          { exploit DISJOINT.
            - symmetry. eapply H.
            - instantiate (1:=to). econs; ss. refl.
            - econs; ss. apply memory_get_ts_le in GET; eauto.
            - auto. }
          { inv H0. exfalso. eapply ATTACH; eauto. }
        }
        { exfalso. destruct FROM.
          { exploit DISJOINT.
            - symmetry. eapply H.
            - instantiate (1:=to). econs; ss. refl.
            - econs; ss. apply memory_get_ts_le in GET; eauto.
            - auto. }
          { inv H0. exfalso. eapply ATTACH; eauto. }
        }

    - des. clarify.
      exploit split_succeed_wf; try apply PROMISES. i. des.
      dup GET2. apply WFTGT in GET0.
      dup PROMISE. specialize (PROMISE0 loc ts3).
      rewrite GET2 in PROMISE0.

      assert (exists from_src, <<GETSRC: Memory.get loc ts3 prom_src = Some (from_src, Message.reserve)>>).
      { inv PROMISE0; eauto. clarify. } des. rewrite GETSRC in *.

      assert (EMPTY0: forall ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3),
                 Memory.get loc ts' mem_tgt = None).
      { i. destruct (Memory.get loc ts' mem_tgt) as [[from' msg']|] eqn:GET; auto.
        exfalso. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - eapply x0.
          + instantiate (1:=ts'). econs; ss; [|refl].
            apply memory_get_ts_strong in GET. des; clarify; auto.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            * eapply TS0.
            * eapply Time.bot_spec.
          + econs; ss. left. auto. }

      assert (EMPTY1: forall to' msg' ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3)
                             (GET: Memory.get loc to' mem_tgt = Some (ts', msg')),
                 False).
      { i. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - hexploit memory_get_to_mon.
          { eapply GET0. }
          { eapply GET. }
          { auto. } i.
          eapply x0.
          + instantiate (1:=ts3). econs; ss. left. auto.
          + econs; ss; [|refl]. etrans; eauto. }

      exploit (@promises_not_attached_replace_split self loc from_src (Time.middle from to) to ts3 prom_src mem_src); auto.
      { i. specialize (PROMISE loc to0). rewrite GET in *. inv PROMISE; clarify. }
      { eapply (@TimeFacts.le_lt_lt _ from); eauto. eapply Time.bot_spec. }
      { eapply Time.middle_spec; eauto. }
      { ii. inv H.
        assert (exists from0' msg', <<GETTGT: Memory.get loc to0 mem_tgt = Some (from0', msg')>> /\ <<TS: Time.le from0' from0>>).
        { dup MEM. specialize (MEM loc to0). rewrite GET in MEM. inv MEM; eauto. } des.
        assert (TS1: Time.lt to0 ts3).
        { eapply memory_get_to_mon; try apply GET; eauto.
          inv ITV0. inv ITV. ss. eapply TimeFacts.lt_le_lt; eauto. }
        erewrite EMPTY0 in GETTGT.
        - clarify.
        - inv ITV. inv ITV0. ss. eapply TimeFacts.lt_le_lt.
          { eapply Time.middle_spec; eauto. }
          { left. eapply TimeFacts.lt_le_lt; eauto. }
        - auto.
      }

      intros [prom_src' [mem_src' ?]]. des.

      assert (PROMISEDDIFF: promised prom_src' =
                            fun loc' =>
                              if (Loc.eq_dec loc' loc)
                              then fun ts' => if (Time.eq_dec ts' to) then True else promised prom_src loc' ts'
                              else promised prom_src loc').
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H. erewrite PROMSPEC in GET. des_ifs; try by (ss; des; clarify).
          + ss. des; clarify. econs; eauto.
          + ss. des; clarify. econs; eauto.
          + econs; eauto.
        - specialize (PROMSPEC loc' ts'). des_ifs; try by (ss; des; clarify).
          + econs; eauto.
          + econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'). splits; auto.
      + ii. erewrite MEMSPEC.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs 3; eauto.
          { left. apply Time.middle_spec; eauto. }
        * ss. des; clarify.
          specialize (MEM loc ts3). rewrite GET0 in *.
          apply WFSRC in GETSRC. rewrite GETSRC in *. inv MEM; eauto.
          { econs 2; eauto. refl. }
          { econs 3; eauto. refl. }
      + ii. erewrite MEMSPEC in GET. des_ifs.
        * ss. des; clarify. exfalso.
          specialize (MEM loc (Time.middle from to)).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H.
          { clarify. }
          { eapply Time.middle_spec; eauto. }
          { etrans; eauto. eapply Time.middle_spec; eauto. }
        * ss. des; clarify. exfalso.
          specialize (MEM loc from0).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H; auto.
          { clarify. }
        * eauto.
      + ii. erewrite PROMSPEC.
        erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. inv PROMISE0; eauto.
      + ii. erewrite MEMSPEC in GET. erewrite PROMISEDDIFF.
        des_ifs; eauto; try by (ss; des; clarify).
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. exfalso.
          exploit (@memory_get_from_inj mem_src' loc to ts1 ts3 msg Message.reserve).
          { erewrite MEMSPEC. des_ifs; ss; des; clarify. }
          { erewrite MEMSPEC. des_ifs; ss; des; clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          i. des; clarify.
          { eapply Time.lt_strorder; eauto. }

    - dup PROMISES. apply Memory.lower_get0 in PROMISES0. des. clarify.
      dup GET. apply WFTGT in GET1.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; clarify.
      exists prom_src, mem_src, self. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify.
        specialize (MEM loc to). rewrite GET1 in *. inv MSG_LE. inv MEM; eauto.
        { exfalso. eapply NPROM. auto. }
      + ii. eauto.
      + ii. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. inv MSG_LE. rewrite <- H0. econs 4; eauto.

    - hexploit Memory.remove_get0; try apply PROMISES. i. des.
      dup GET. apply WFTGT in GET1.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; clarify.

      hexploit (@Memory.remove_exists prom_src loc from_src to Message.reserve).
      { auto. }
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src loc from_src to Message.reserve); eauto.
      intros [mem_src' REMOVEMEM].
      assert (PROMISESRC: Memory.promise prom_src mem_src loc from_src to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      assert (FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src').
      { eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then False else self loc' ts').
      splits; auto.
      + ii. erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto.
        des_ifs; ss; des; clarify. econs. ii. des; clarify.
        eapply EXCLUSIVE; eauto. econs; eauto.
      + ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs. ss.
      + ii. erewrite Memory.remove_o in GET2; eauto.
        erewrite promised_remove; eauto. des_ifs; eauto.
        ss. des; clarify.
  Qed.

  Lemma sim_write_forget others self mem_src mem_tgt prom_src prom_tgt
        loc from from' to val released prom_tgt'
        (STEPTGT: Memory.remove prom_tgt loc from to (Message.concrete val released) prom_tgt')
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SELF: self loc to)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (EXCLUSIVE: forall loc' ts' (SELF: self loc' ts') (OTHER: others loc' ts'), False)

        (FROM: Time.le from from')
        (FROMTO: Time.lt from' to)

        (CONSISTENT: forall ts (TS: Time.lt ts to), ~ concrete_promised prom_tgt loc ts)
        (ATTACHED: from = from' -> concrete_promised mem_src loc from)

        (ADDCLOSED: semi_closed_opt_view released mem_src loc to)
        (VIEWWF: View.opt_wf released)
        (MSGTO: Time.le (View.rlx (View.unwrap released) loc) to)

    :
      exists self' prom0 prom1 mem0 mem1 prom_src' mem_src',
        (<<FUTURE01: reserve_future_memory prom_src mem_src prom0 mem0>>) /\
        (<<STEPSRC: Memory.write prom0 mem0 loc from' to val released prom1 mem1 Memory.op_kind_add>>) /\
        (<<FUTURE23: reserve_future_memory prom1 mem1 prom_src' mem_src'>>) /\

        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self' prom_src' prom_tgt'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised prom_src') mem_src'>>)
  .
  Proof.
    dup STEPTGT. eapply Memory.remove_get0 in STEPTGT0. des.
    dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in PROMISE0.
    inv PROMISE0; clarify. rename H0 into GETSRC. symmetry in GETSRC.
    exploit promises_not_attached_replace_write; eauto.
    { i. specialize (PROMISE loc to0). rewrite GET1 in *.
      inv PROMISE; eauto. clarify. }
    { eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec. }
    { ii. inv H.
      assert (exists from_tgt msg_tgt,
                 (<<GETTGT0: Memory.get loc to0 mem_tgt = Some (from_tgt, msg_tgt)>>)).
      { dup MEM. specialize (MEM0 loc to0).
        rewrite GET1 in MEM0. inv MEM0; eauto. } des.
      exploit Memory.get_disjoint.
      { eapply GETTGT0. }
      { eapply WFTGT. eapply GET. } i. des; clarify.
      - dup GETSRC. apply WFSRC in GETSRC0. clarify.
        inv ITV. inv ITV0. ss.
        eapply Time.lt_strorder. eapply (@TimeFacts.lt_le_lt from0 ts); eauto.
      - eapply x0.
        + instantiate (1:=ts). econs; ss.
          * inv ITV. inv ITV0. ss.
            eapply TimeFacts.le_lt_lt; eauto.
            specialize (MEM loc to0).
            rewrite GET1 in *. rewrite GETTGT0 in *. inv MEM; ss.
          * inv ITV0. ss.
        + inv ITV; ss. econs; ss.
          * eapply TimeFacts.le_lt_lt; eauto.
          * etrans; eauto. eapply memory_get_ts_le; eauto. }
    i. des.

    exists (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                            then False else self loc' ts'),
    prom1, prom2, mem1, mem2, prom3, mem3. splits; eauto.
    - ii. erewrite MEMSPEC. des_ifs.
      + ss. des; clarify.
        dup GET. eapply WFTGT in GET. rewrite GET. econs 2; eauto.
        * ii. des; eauto.
        * i. clarify.
    - ii. erewrite MEMSPEC in GET1. des_ifs; eauto.
      ss. des; clarify.
      dup MEM. specialize (MEM0 loc from0). inv MEM0; try by (exfalso; eauto).
      clear PROM0. exploit Memory.get_disjoint.
      { symmetry. eapply H. }
      { apply WFTGT. apply GET. }
      i. des; clarify.
      { exfalso. eapply Time.lt_strorder; eauto. }
      destruct FROM.
      { exfalso. eapply x0.
        - instantiate (1:=from0). econs; ss.
          + symmetry in H. apply memory_get_ts_strong in H. des; auto.
            clarify. exfalso. eapply Time.lt_strorder.
            eapply (@TimeFacts.le_lt_lt Time.bot from); eauto.
            eapply Time.bot_spec.
          + refl.
        - econs; ss. left. auto. }
      { inv H1. exploit ATTACHED; eauto. i. inv x. rewrite GET1 in *. clarify. }
    - ii. erewrite PROMSPEC. erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
      + ss. des; clarify. econs; eauto.
    - ii. erewrite MEMSPEC in GET1. des_ifs.
      + ss. des; clarify.
        exfalso. eapply CONSISTENT; eauto.
        specialize (PROMISE loc ts0). inv PROMISE; clarify. econs; eauto.
      + exploit PROMATTACH; eauto. i. inv x.
        specialize (PROMSPEC loc0 ts1). des_ifs.
        * ss. des; clarify.
        * erewrite <- PROMSPEC in *. econs; eauto.
  Qed.

  Lemma reserve_future_memory_steps
        lang st vw sc prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      exists tr,
        (<<STEPS: Trace.steps tr
                              (Thread.mk lang st (Local.mk vw prom0) sc mem0)
                              (Thread.mk lang st (Local.mk vw prom1) sc mem1)>>).
  Proof.
    ginduction FUTURE; eauto. i. exploit IHFUTURE; eauto. i. des.
    esplits. eapply Trace.steps_trans; [|apply STEPS|ss].
    econs 1. econs; eauto.
  Qed.

  Lemma reserve_future_memory_unchangable
        prom0 mem0 prom1 mem1 loc to from msg
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (UNCH: unchangable mem0 prom0 loc to from msg)
    :
      unchangable mem1 prom1 loc to from msg.
  Proof.
    ginduction FUTURE; eauto. i. exploit IHFUTURE; eauto.
    eapply unchangable_promise; eauto.
  Qed.

  Lemma reserve_future_memory_future
        vw sc prom0 mem0 prom1 mem1
        (LOCAL: Local.wf (Local.mk vw prom0) mem0)
        (SC: Memory.closed_timemap sc mem0)
        (MEM: Memory.closed mem0)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      (<<LOCAL: Local.wf (Local.mk vw prom1) mem1>>) /\
      (<<SC: Memory.closed_timemap sc mem1>>) /\
      (<<MEM: Memory.closed mem1>>).
  Proof.
    ginduction FUTURE; eauto. i.
    exploit Local.promise_step_future.
    { econs.
      - instantiate (9:=Local.mk vw prom0). eauto.
      - eauto.
      - eauto. }
    all: eauto. i. des. ss. eapply IHFUTURE; eauto.
  Qed.

  Lemma sim_write_step_forget
        others self pasts vw_src prom_src lc_tgt sc mem_src mem_tgt
        lc_tgt' sc' mem_tgt' loc from to val ord releasedm released kind_tgt from'
        (LOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf (Local.mk vw_src prom_src) mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self (Local.mk vw_src prom_src) lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (CONSISTENT: Local.promise_consistent lc_tgt')
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src prom_src loc' ts' from msg>>)

        (FROM: Time.le from from')
        (FROMTO: Time.lt from' to)

        (ATTACHED: from = from' -> concrete_promised mem_src loc from)

        (RELEASEDMCLOSEDSRC: Memory.closed_opt_view releasedm mem_src)
        (RELEASEDMCLOSEDTGT: Memory.closed_opt_view releasedm mem_tgt)
        (RELEASEDMWF: View.opt_wf releasedm)
    :
      exists self' vw_src' prom_src' mem_src'
             prom0 prom1 mem0 mem1 kind_src,
        (<<FUTURE01: reserve_future_memory prom_src mem_src prom0 mem0>>) /\
        (<<STEPSRC: Local.write_step (Local.mk vw_src prom0) sc mem0 loc from' to val releasedm released ord (Local.mk vw_src' prom1) sc' mem1 kind_src>>) /\
        (<<FUTURE12: reserve_future_memory prom1 mem1 prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised prom_src') mem_src'>>) /\
        (<<SIM: sim_local self' (Local.mk vw_src' prom_src') lc_tgt'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv SIM. inv LOCALSRC. inv LOCALTGT. inv STEPTGT. inv WRITE. ss.
    exploit sim_promise_step_forget; eauto.
    { i. exploit EXCLUSIVE; eauto. i. des. inv UNCH. inv SELF. clarify. }
    i. des.

    hexploit Local.write_step_future; eauto. i. des. ss.
    hexploit reserve_future_memory_future; try apply STEPSRC; eauto. i. des.
    inv LOCAL. ss.

    hexploit sim_write_forget.
    { eauto. }
    { eauto. }
    { specialize (PROMISE0 loc to).
      eapply Memory.remove_get0 in REMOVE. des. erewrite GET in *.
      inv PROMISE0; clarify. }
    { eauto. }
    { admit. }
    { eauto. }
    { admit. }
    { eauto. }
    { eauto. }
    { ii. exploit EXCLUSIVE; eauto. i. des.
      eapply reserve_future_memory_unchangable in UNCH; eauto.
      specialize (PROMISE0 loc' ts'). inv UNCH. rewrite NPROM in *.
      inv PROMISE0; eauto. }
    { eapply FROM. }
    { eauto. }

    { ii. inv H. eapply Memory.remove_get1 in GET; eauto. des; clarify.
      - eapply Time.lt_strorder; eauto.
      - exploit CONSISTENT; eauto. ss. i. eapply Time.lt_strorder. etrans.
        { eapply x. } eapply TimeFacts.lt_le_lt.
        { eapply TS. } unfold TimeMap.join, TimeMap.singleton.
        setoid_rewrite LocFun.add_spec_eq. eapply Time.join_r. }
    { i. exploit ATTACHED; eauto. i. inv x.
      eapply Memory.future_get1 in GET.
      { des. inv MSG_LE. econs; eauto. }
      { eapply reserve_future_future; eauto. }
    }
    { unfold TView.write_released. des_ifs; econs.
      eapply semi_closed_view_join.
      - inv MEM1. eapply unwrap_closed_opt_view; eauto.
        eapply closed_opt_view_semi_closed.
        eapply Memory.future_closed_opt_view.
        + eapply reserve_future_future; eauto.
        + eauto.
      - eapply semi_closed_view_future; cycle 1.
        { eapply Memory.future_future_weak.
          eapply reserve_future_future; eauto. }
        ss. inv TVIEW_CLOSED. setoid_rewrite LocFun.add_spec_eq. des_ifs.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. eauto.
          * inv MEMSRC. eapply semi_closed_view_singleton; eauto.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. eauto.
          * inv MEMSRC. eapply semi_closed_view_singleton; eauto.
    }
    { exploit TViewFacts.write_future0; eauto. i. des. eauto. }
    {

          eapply semi_closed_opt_view_future; eauto.

        Memory.future_weak_closed_view
        eapply semi_

               Memory.closed_view

        admit.
      -


      eapply add_

      eapply TViewFacts.write_released_mon; eauto. refl. }
    { eapply write_released_add_closed; auto.
      { eapply add_closed_opt_view_future_add_closed.
        - eapply Memory.future_future_weak. eapply reserve_future_future; eauto.
        - eapply closed_add_closed_opt_view; eauto. }
      { refl. }
    }
    { eapply TViewFacts.write_future0; eauto. }
    { etrans; eauto. exploit TViewFacts.write_released_mon.
      { eapply TVIEW. }
      { eapply SC. }
      { eauto. }
      { eapply RELEASEDMLE. }
      { eauto. }
      { refl. } i. apply View.unwrap_opt_le in x0. inv x0. eauto. }
    i. des.
    eexists pasts', self'0, _, prom_src'0, sc_src, mem_src'0,
    prom0, prom1, mem0, mem1. esplits; eauto.
    { eapply reserve_future_memory_trans; eauto. }
    { econs; eauto.
      - ss. inv TVIEW. eapply TViewFacts.writable_mon; eauto. refl.
      - ii. ss. des_ifs. inv STEPSRC0. inv PROMISE2. ss.
        exploit MemoryMerge.MemoryMerge.add_remove.
        { eapply PROMISES2. }
        { eapply REMOVE0. }
        i. clarify.
        eapply reserve_future_concrete_same_promise in GET; eauto.
        specialize (PROMISE1 loc t). rewrite GET in *. inv PROMISE1; clarify. }
    { etrans; eauto. }
    { ss. econs; ss.
      - eapply TViewFacts.write_tview_mon; eauto. refl.
      - ii. specialize (PROMISE1 loc0 ts). dup PROMISE1.
        inv PROMISE1; eauto. setoid_rewrite LocFun.add_spec_neq; auto.
        ii. clarify. }
  Qed.



    { eauto. }
    { eauto. }
    { specialize (PROMISE0 loc to).
      eapply Memory.remove_get0 in REMOVE. des. erewrite GET in *.
      inv PROMISE0; clarify. }
    { eauto. }
    { admit. }
    { eauto. }
    { admit. }
      (* inv WF2. eapply promise_memory_le; cycle 1; eauto. } *)
    { eauto. }
    { eapply reserve_future_wf_pasts_memory; eauto. }
    { eauto. }
    { ii. exploit EXCLUSIVE; eauto. i. des.
      eapply reserve_future_memory_unchangable in UNCH; eauto.
      specialize (PROMISE0 loc' ts'). inv UNCH. rewrite NPROM in *.
      inv PROMISE0; eauto. }
    { eapply FROM. }
    { eauto. }
    { ii. inv H. eapply Memory.remove_get1 in GET; eauto. des; clarify.
      - eapply Time.lt_strorder; eauto.
      - exploit CONSISTENT; eauto. ss. i. eapply Time.lt_strorder. etrans.
        { eapply x. } eapply TimeFacts.lt_le_lt.
        { eapply TS. } unfold TimeMap.join, TimeMap.singleton.
        setoid_rewrite LocFun.add_spec_eq. eapply Time.join_r. }
    { i. exploit ATTACHED; eauto. i. inv x.
      eapply Memory.future_get1 in GET.
      { des. inv MSG_LE. econs; eauto. }
      { eapply reserve_future_future; eauto. }
    }
    { eapply TViewFacts.write_released_mon; eauto. refl. }
    { eapply write_released_add_closed; auto.
      { eapply add_closed_opt_view_future_add_closed.
        - eapply Memory.future_future_weak. eapply reserve_future_future; eauto.
        - eapply closed_add_closed_opt_view; eauto. }
      { refl. }
    }
    { eapply TViewFacts.write_future0; eauto. }
    { etrans; eauto. exploit TViewFacts.write_released_mon.
      { eapply TVIEW. }
      { eapply SC. }
      { eauto. }
      { eapply RELEASEDMLE. }
      { eauto. }
      { refl. } i. apply View.unwrap_opt_le in x0. inv x0. eauto. }
    i. des.
    eexists pasts', self'0, _, prom_src'0, sc_src, mem_src'0,
    prom0, prom1, mem0, mem1. esplits; eauto.
    { eapply reserve_future_memory_trans; eauto. }
    { econs; eauto.
      - ss. inv TVIEW. eapply TViewFacts.writable_mon; eauto. refl.
      - ii. ss. des_ifs. inv STEPSRC0. inv PROMISE2. ss.
        exploit MemoryMerge.MemoryMerge.add_remove.
        { eapply PROMISES2. }
        { eapply REMOVE0. }
        i. clarify.
        eapply reserve_future_concrete_same_promise in GET; eauto.
        specialize (PROMISE1 loc t). rewrite GET in *. inv PROMISE1; clarify. }
    { etrans; eauto. }
    { ss. econs; ss.
      - eapply TViewFacts.write_tview_mon; eauto. refl.
      - ii. specialize (PROMISE1 loc0 ts). dup PROMISE1.
        inv PROMISE1; eauto. setoid_rewrite LocFun.add_spec_neq; auto.
        ii. clarify. }
  Qed.

  Lemma reserve_future_read_commute
        vw0 prom0 mem0 loc to val released ord vw1 prom' prom1 mem1
        (READ: Local.read_step (Local.mk vw0 prom0) mem0 loc to val released ord (Local.mk vw1 prom'))
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Local.read_step (Local.mk vw0 prom1) mem1 loc to val released ord (Local.mk vw1 prom1).
  Proof.
    inv READ. clarify. econs; eauto.
    eapply reserve_future_concrete_same; eauto.
  Qed.

  Lemma sim_thread_step others self pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ self) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self (promised lc_src.(Local.promises)) mem_src)
        (CONSISTENT: Local.promise_consistent lc_tgt')
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from msg>>)
    :
      exists tr self' pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT.

    - inv STEP. destruct (classic (L loc)).
      + inv LOCAL. inv SIM. inv LOCALSRC. inv LOCALTGT.
        exploit sim_promise_step_forget; eauto.
        { i. exploit EXCLUSIVE; eauto. i. des. inv UNCH. inv SELF. clarify. }
        i. des. destruct lc_src.
        exploit reserve_future_memory_steps; eauto. i. des.
        eexists _, self', pasts, (Local.mk _ _), _, mem_src'. splits; eauto.
        * econs; ss.
        * eapply reserve_future_wf_pasts_memory; eauto.
        * refl.
      + inv LOCAL. inv SIM. inv LOCALSRC. inv LOCALTGT.
        exploit sim_promise_step_normal; try apply MEM; eauto.
        { inv TVIEW_WF. eauto. }
        { i. clarify. transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
          - transitivity (View.rlx (TView.rel (Local.tview lc_tgt) loc) loc).
            + inv TVIEW. specialize (REL loc). inv REL. auto.
            + inv TVIEW_WF0. specialize (REL_CUR loc). inv REL_CUR. auto.
          - exploit CONSISTENT; ss; eauto.
            + eapply Memory.promise_get0 in PROMISE.
              * des. eauto.
              * inv PROMISE; clarify.
            + i. left. auto. }
        { inv TVIEW_CLOSED. eauto. }
        i. des.
        eexists [(_, ThreadEvent.promise loc from to msg_src kind_src)], self, pasts', (Local.mk _ _), _, mem_src'.
        splits; ss.
        * econs 2; [|econs 1|ss]. econs 1. econs; eauto.
        * ss.
        * ss.

    - inv STEP. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], self, pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released_src ord)],
        self, pasts, lc_src', sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
        * inv STEPSRC; ss.
      + destruct (classic (L loc)).
        * assert (TS: Time.lt from to).
          { inv LOCAL0. inv WRITE. inv PROMISE; ss.
            - eapply add_succeed_wf in MEM0. des. auto.
            - eapply split_succeed_wf in MEM0. des. auto.
            - eapply lower_succeed_wf in MEM0. des. auto. }
          assert (MIDDLE: Time.lt (Time.middle from to) to).
          { eapply Time.middle_spec; eauto. }
          destruct lc_src. hexploit sim_write_step_forget; eauto.
          { left. eapply Time.middle_spec; eauto. }
          { i. exfalso. eapply Time.lt_strorder.
            instantiate (1:=from). erewrite H0 at 2. eapply Time.middle_spec; eauto. }
          i. des.
          eapply reserve_future_memory_steps in FUTURE01. des.
          eapply reserve_future_memory_steps in FUTURE12. des.
          esplits; eauto.
          { eapply Trace.steps_app.
            { eapply STEPS. }
            eapply Trace.steps_app.
            { econs 2; [|econs 1|ss]. econs 2. econs; cycle 1.
              - econs 3. eauto.
              - ss. eauto. }
            eauto.
          }
          { ss. }
        * hexploit sim_write_step_normal; try apply MEM; try eassumption.
          { i. instantiate (1:=None). econs. }
          { i. clarify. }
          { econs. }
          { econs. }
          { econs. }
          { econs. } i. des.
          eexists [(_, ThreadEvent.write loc from to val _ ord)], self, pasts', lc_src', _, mem_src'.
          splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + destruct (classic (L loc)).
        * assert (TS: Time.lt tsr tsw).
          { inv LOCAL2. inv WRITE. inv PROMISE; ss.
            - eapply add_succeed_wf in MEM0. des. auto.
            - eapply split_succeed_wf in MEM0. des. auto.
            - eapply lower_succeed_wf in MEM0. des. auto. }

          exploit sim_read_step; eauto. i. des.
          exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
          exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.

          dup STEPSRC. inv STEPSRC. destruct lc_src. ss. clarify.
          hexploit sim_write_step_forget; eauto.
          { refl. }
          { i. econs; eauto. }
          i. des.
          eapply reserve_future_read_commute in STEPSRC0; eauto.
          eapply reserve_future_memory_steps in FUTURE01. des.
          eapply reserve_future_memory_steps in FUTURE12. des.
          esplits; try apply MEM0; eauto.
          { eapply Trace.steps_app.
            { eapply STEPS. }
            eapply Trace.steps_app.
            { econs 2; [|econs 1|ss]. econs 2. econs; cycle 1.
              - econs 4; eauto.
              - ss. eauto. }
            eauto.
          }
          { ss. }
        * exploit sim_read_step; eauto. i. des.
          dup PAST. inv PAST0. exploit COMPLETE; eauto. i. des.
          exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
          exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.
          hexploit sim_write_step_normal; try apply MEM; try eassumption.
          { inv STEPSRC. ss. }
          { i. clarify. }
          { i. eauto. } i. des.
          eexists [(_, ThreadEvent.update loc tsr tsw valr valw released_src released_src0 ordr ordw)],
          self, pasts', lc_src'0, sc_src', mem_src'. splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        self, pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
        * inv STEPSRC; ss.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.syscall e)],
        self, pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
        * inv STEPSRC; ss.
      + exploit sim_failure_step; eauto. i. des.
        eexists [(_, ThreadEvent.failure)],
        self, pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
  Qed.

End SIM.
