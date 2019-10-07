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
Require Import MemoryMerge.

Require Import FulfillStep.

Require Import Promotion.

Set Implicit Arguments.


Module SimCommon.
  (* simulation relations *)

  Definition sim_timemap (l: Loc.t) (tm_src tm_tgt: TimeMap.t): Prop :=
    forall loc (LOC: loc <> l), tm_src loc = tm_tgt loc.

  Inductive sim_view (l: Loc.t) (view_src view_tgt: View.t): Prop :=
  | sim_view_intro
      (PLN: sim_timemap l view_src.(View.pln) view_tgt.(View.pln))
      (RLX: sim_timemap l view_src.(View.rlx) view_tgt.(View.rlx))
  .
  Hint Constructors sim_view.

  Inductive sim_opt_view (l: Loc.t): forall (view_src view_tgt: option View.t), Prop :=
  | sim_opt_view_some
      view_src view_tgt
      (SIM: sim_view l view_src view_tgt):
      sim_opt_view l (Some view_src) (Some view_tgt)
  | sim_opt_view_none:
      sim_opt_view l None None
  .
  Hint Constructors sim_opt_view.

  Inductive sim_tview (l: Loc.t) (tview_src tview_tgt: TView.t): Prop :=
  | sim_tview_intro
      (REL: forall loc, sim_view l (tview_src.(TView.rel) loc) (tview_tgt.(TView.rel) loc))
      (CUR: sim_view l tview_src.(TView.cur) tview_tgt.(TView.cur))
      (ACQ: sim_view l tview_src.(TView.acq) tview_tgt.(TView.acq))
  .
  Hint Constructors sim_tview.

  Inductive sim_message (l: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
  | sim_message_full
      val released_src released_tgt
      (RELEASED: sim_opt_view l released_src released_tgt):
      sim_message l (Message.full val released_src) (Message.full val released_tgt)
  | sim_message_reserve:
      sim_message l Message.reserve Message.reserve
  .
  Hint Constructors sim_message.

  Inductive sim_memory (l: Loc.t) (mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: forall loc from to msg_src
                (LOC: loc <> l)
                (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
          exists msg_tgt,
            <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
            <<MSG: sim_message l msg_src msg_tgt>>)
      (COMPLETE: forall loc from to msg_tgt
                   (LOC: loc <> l)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
          exists msg_src,
            <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
            <<MSG: sim_message l msg_src msg_tgt>>)
  .
  Hint Constructors sim_memory.

  Inductive sim_local (l: Loc.t) (lc_src lc_tgt: Local.t): Prop :=
  | sim_local_intro
      (TVIEW: sim_tview l lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMISES1: sim_memory l lc_src.(Local.promises) lc_tgt.(Local.promises))
  .
  Hint Constructors sim_local.


  (* fulfillable *)

  Definition view_le_loc (l: Loc.t) (view1 view2: View.t): Prop :=
    <<PLN: Time.le (view1.(View.pln) l) (view2.(View.pln) l)>> /\
    <<RLX: Time.le (view1.(View.rlx) l) (view2.(View.rlx) l)>>.

  Global Program Instance view_le_loc_PreOrder: forall l, PreOrder (view_le_loc l).
  Next Obligation.
    ii. econs; unnw; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0.
    econs; unnw; etrans; eauto.
  Qed.

  Definition tview_released_le_loc (l loc: Loc.t) (tview: TView.t) (released: View.t): Prop :=
    view_le_loc l (tview.(TView.rel) loc) released.

  Definition prev_released_le_loc (l loc: Loc.t) (from: Time.t) (mem: Memory.t) (released: View.t): Prop :=
    match Memory.get loc from mem with
    | Some (_, Message.full _ (Some r)) => view_le_loc l r released
    | _ => True
    end.

  Definition fulfillable (l: Loc.t) (tview: TView.t) (mem promises: Memory.t): Prop :=
    forall loc from to val released
      (GETP: Memory.get loc to promises =
             Some (from, Message.full val (Some released))),
      <<TVIEW: tview_released_le_loc l loc tview released>> /\
      <<PREV: prev_released_le_loc l loc from mem released>>.


  (* generating source message *)

  Definition get_released_src (strong: bool) (l loc: Loc.t) (released_tgt: View.t)
             (tview_src: TView.t) (released_prev: View.t): View.t :=
    if strong
    then
      View.mk
        (LocFun.add
           l (Time.join (tview_src.(TView.cur).(View.pln) l) (released_prev.(View.pln) l))
           released_tgt.(View.pln))
        (LocFun.add
           l (Time.join (tview_src.(TView.cur).(View.rlx) l) (released_prev.(View.rlx) l))
           released_tgt.(View.rlx))
    else
      View.mk
        (LocFun.add
           l (Time.join ((tview_src.(TView.rel) loc).(View.pln) l) (released_prev.(View.pln) l))
           released_tgt.(View.pln))
        (LocFun.add
           l (Time.join ((tview_src.(TView.rel) loc).(View.rlx) l) (released_prev.(View.rlx) l))
           released_tgt.(View.rlx)).

  Definition get_message_src (strong: bool) (l loc: Loc.t) (msg_tgt: Message.t)
             (tview_src: TView.t) (from: Time.t) (mem_src: Memory.t): Message.t :=
    match msg_tgt with
    | Message.full val (Some released_tgt) =>
      match (Memory.get loc from mem_src) with
      | Some (_, Message.full _ (Some released_prev)) =>
        Message.full val (Some (get_released_src strong l loc released_tgt tview_src released_prev))
      | _ =>
        Message.full val (Some (get_released_src strong l loc released_tgt tview_src View.bot))
      end
    | _ => msg_tgt
    end.

  Lemma get_released_src_tview_released_le_loc
        strong l loc released_tgt tview_src released_prev
        (TVIEW: TView.wf tview_src):
    <<TVIEW: tview_released_le_loc l loc tview_src (get_released_src strong l loc released_tgt tview_src released_prev)>>.
  Proof.
    unfold get_released_src. condtac; ss.
    - inv TVIEW. destruct (REL_CUR loc).
      econs; ss.
      + unfold LocFun.add. condtac; ss. unnw.
        etrans; try eapply PLN. eapply Time.join_l.
      + unfold LocFun.add. condtac; ss. unnw.
        etrans; try eapply RLX. eapply Time.join_l.
    - econs; ss.
      + unfold LocFun.add. condtac; ss. eapply Time.join_l.
      + unfold LocFun.add. condtac; ss. eapply Time.join_l.
  Qed.

  Lemma get_released_src_prev_released_le_loc
        strong l loc released_tgt tview_src released_prev
        from mem_src from' val
        (GET: Memory.get loc from mem_src = Some (from', Message.full val (Some released_prev))):
    <<PREV: prev_released_le_loc l loc from mem_src (get_released_src strong l loc released_tgt tview_src released_prev)>>.
  Proof.
    unfold prev_released_le_loc. rewrite GET.
    unfold get_released_src, LocFun.add. 
    econs; repeat (condtac; ss); eauto using Time.join_r.
  Qed.

  Lemma get_released_src_sim_view
        strong l loc released_tgt tview_src released_prev:
    <<SIM: sim_view l (get_released_src strong l loc released_tgt tview_src released_prev) released_tgt>>.
  Proof.
    unfold get_released_src. econs; ss.
    - unfold sim_timemap, LocFun.add. i. repeat (condtac; ss).
    - unfold sim_timemap, LocFun.add. i. repeat (condtac; ss).
  Qed.

  Lemma get_released_src_wf
        strong l loc released_tgt tview_src released_prev
        (RELEASED_TGT: View.wf released_tgt)
        (TVIEW_SRC: TView.wf tview_src)
        (RELEASED_PREV: View.wf released_prev):
    View.wf (get_released_src strong l loc released_tgt tview_src released_prev).
  Proof.
    econs. ii.
    unfold get_released_src, LocFun.add. repeat (condtac; ss).
    - subst. inv TVIEW_SRC. inv CUR.
      inv RELEASED_PREV.
      apply Time.join_spec.
      + etrans; eauto. apply Time.join_l.
      + etrans; eauto. apply Time.join_r.
    - inv RELEASED_TGT. apply PLN_RLX.
    - subst. inv TVIEW_SRC. destruct (REL loc).
      inv RELEASED_PREV.
      apply Time.join_spec.
      + etrans; eauto. apply Time.join_l.
      + etrans; eauto. apply Time.join_r.
    - inv RELEASED_TGT. apply PLN_RLX.
  Qed.

  Lemma get_released_src_closed
        strong l loc released_tgt tview_src released_prev
        mem_src mem_tgt
        (SIM: sim_memory l mem_src mem_tgt)
        (MSG_TGT: Memory.closed_view released_tgt mem_tgt)
        (TVIEW_SRC: TView.closed tview_src mem_src)
        (PREV_SRC: Memory.closed_view released_prev mem_src):
    Memory.closed_view (get_released_src strong l loc released_tgt tview_src released_prev) mem_src.
  Proof.
    inv MSG_TGT. inv TVIEW_SRC. inv PREV_SRC.
    unfold get_released_src. condtac; ss.
    - econs; ss; ii.
      + unfold LocFun.add. condtac; ss.
        * subst. inv CUR.
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (PLN loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
      + unfold LocFun.add. condtac; ss.
        * subst. inv CUR.
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (RLX loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
    - econs; ss; ii.
      + unfold LocFun.add. condtac; ss.
        * subst. destruct (REL loc).
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (PLN loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
      + unfold LocFun.add. condtac; ss.
        * subst. destruct (REL loc).
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (RLX loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
  Qed.

  Lemma get_message_src_fulfillable
        strong l loc msg_tgt tview_src from mem_src
        val released
        (TVIEW: TView.wf tview_src)
        (MSG: get_message_src strong l loc msg_tgt tview_src from mem_src =
              Message.full val (Some released)):
    <<TVIEW: tview_released_le_loc l loc tview_src released>> /\
    <<PREV: prev_released_le_loc l loc from mem_src released>>.
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released0; ss.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|] eqn:GET;
      inv MSG; split;
        eauto using get_released_src_tview_released_le_loc;
        eauto using get_released_src_prev_released_le_loc;
        unfold prev_released_le_loc; rewrite GET; ss.
  Qed.

  Lemma get_message_src_sim_message
        strong l loc msg_tgt tview_src from mem_src:
    <<SIM: sim_message l (get_message_src strong l loc msg_tgt tview_src from mem_src) msg_tgt>>.
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released; ss.
    - destruct (Memory.get loc from mem_src) as [[? [? []|]]|];
        econs; econs; eapply get_released_src_sim_view.
    - econs. econs.
  Qed.

  Lemma get_message_src_wf
        strong l loc msg_tgt tview_src from mem_src
        (MSG_TGT: Message.wf msg_tgt)
        (TVIEW_SRC: TView.wf tview_src)
        (CLOSED_SRC: Memory.closed mem_src):
    Message.wf (get_message_src strong l loc msg_tgt tview_src from mem_src).
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released; ss.
    inv MSG_TGT. inv WF.
    specialize View.bot_wf. i.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|] eqn:GET;
      econs; econs; eauto using get_released_src_wf.
    inv CLOSED_SRC. exploit CLOSED; eauto. i. des.
    inv MSG_WF. inv WF.
    eauto using get_released_src_wf.
  Qed.

  Lemma get_message_src_message_to
        strong l loc to msg_tgt tview_src from mem_src
        (MSG_TGT: Memory.message_to msg_tgt loc to)
        (LOC: loc <> l):
    Memory.message_to (get_message_src strong l loc msg_tgt tview_src from mem_src) loc to.
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released; ss.
    inv MSG_TGT.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|] eqn:GET;
      econs; ss; unfold get_released_src, LocFun.add; repeat (condtac; ss).
  Qed.

  Lemma get_message_src_closed
        strong l loc msg_tgt tview_src from mem1_src mem2_src mem2_tgt
        (SIM: sim_memory l mem2_src mem2_tgt)
        (MSG_TGT: Memory.closed_message msg_tgt mem2_tgt)
        (TVIEW1_SRC: TView.closed tview_src mem1_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (OP_SRC: forall v (CLOSED: Memory.closed_view v mem1_src),
            Memory.closed_view v mem2_src):
    Memory.closed_message (get_message_src strong l loc msg_tgt tview_src from mem1_src) mem2_src.
  Proof.
    inv MSG_TGT; ss. inv CLOSED; eauto.
    exploit Memory.closed_view_bot; try eapply MEM1_SRC. i.
    exploit OP_SRC; eauto. i.
    assert (TVIEW2_SRC: TView.closed tview_src mem2_src).
    { inv TVIEW1_SRC. econs; eauto. }
    destruct (Memory.get loc from mem1_src) as [[? [? []|]]|] eqn:GET;
      econs; econs; eapply get_released_src_closed; eauto.
    inv MEM1_SRC. exploit CLOSED; eauto. i. des.
    inv MSG_CLOSED. inv CLOSED1. eauto.
  Qed.

  Lemma get_message_src_full
        strong l loc msg_tgt tview_src from mem_src
        val released
        (MSG: get_message_src strong l loc msg_tgt tview_src from mem_src = Message.full val released):
    exists released_tgt, msg_tgt = Message.full val released_tgt.
  Proof.
    destruct msg_tgt; ss.
    destruct released0; try by inv MSG; eauto.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|]; inv MSG; eauto.
  Qed.

  Lemma get_message_src_reserve
        strong l loc msg_tgt tview_src from mem_src
        (MSG: get_message_src strong l loc msg_tgt tview_src from mem_src = Message.reserve):
    msg_tgt = Message.reserve.
  Proof.
    destruct msg_tgt; ss.
    destruct released; ss.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|]; ss.
  Qed.


  (* promise *)

  Lemma promise
        l tview_src
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_memory l promises1_src promises1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (FULFILL1: fulfillable l tview_src mem1_src promises1_src)
        (TVIEW_SRC: TView.wf tview_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (LOC: loc <> l):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to
                                    (get_message_src false l loc msg_tgt tview_src from mem1_src)
                                    promises2_src mem2_src kind_src>> /\
      <<PROMISES2: sim_memory l promises2_src promises2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILL2: fulfillable l tview_src mem2_src promises2_src>>.
  Proof.
    inv PROMISES1. inv MEM1. inv PROMISE_TGT.
    { (* add *)
      exploit (@Memory.add_exists mem1_src loc from to
                                  (get_message_src false l loc msg_tgt tview_src from mem1_src)).
      { ii. exploit SOUND0; eauto. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des.
        { subst. congr. }
        apply (x2 x); eauto. }
      { inv MEM. inv ADD. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv ADD. ss. }
      i. des.
      exploit Memory.add_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs; eauto.
        + eapply get_message_src_message_to; eauto.
        + i. exploit get_message_src_reserve; eauto. i. subst.
          exploit RESERVE; eauto. i. des.
          exploit COMPLETE0; try exact x; eauto. i. des.
          inv MSG. eauto.
        + i. exploit SOUND0; try exact GET; eauto. i. des.
          destruct msg_tgt; ss. eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - ii. revert GETP. erewrite Memory.add_o; eauto. condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss.
          des. subst. inv x0. inv ADD. timetac.
        + guardH o.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss. des. subst.
          destruct (get_message_src false l loc msg_tgt tview_src from mem1_src) eqn:GET; ss.
          exploit get_message_src_full; eauto. i. des. subst.
          exploit LE1_SRC; try exact GETP. i.
          exploit SOUND0; try exact x; eauto. i. des. inv MSG.
          exploit ATTACH; eauto; ss.
    }

    { (* split *)
      guardH RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      clear GET GET1 GET2.
      exploit COMPLETE; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3
                                    (get_message_src false l loc msg_tgt tview_src from mem1_src) msg_src); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv SPLIT. ss. }
      i. des.
      exploit Memory.split_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 2; eauto.
        + eapply get_message_src_message_to; eauto.
        + unguard. des. subst.
          unfold get_message_src.
          destruct released'; eauto.
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|]; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - ii. revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. inv x0. inv SPLIT. timetac.
          * guardH o. des. subst.
            inv x0. inv SPLIT. rewrite TS12 in TS23. timetac.
        + guardH o. des. subst. inv GETP.
          exploit FULFILL1; try exact GET_SRC. i. des. split; auto.
          exploit Memory.split_get0; try exact x1. i. des.
          unfold prev_released_le_loc. rewrite GET2.
          destruct msg_tgt as [? []|]; ss.
          assert (BOT: view_le_loc l (get_released_src false l loc t tview_src View.bot) released).
          { exploit FULFILL1; try exact GET_SRC. i. des.
            inv TVIEW0. econs; ss.
            - unfold LocFun.add. condtac; ss.
              eapply Time.join_spec; eauto.
              unfold TimeMap.bot. apply Time.bot_spec.
            - unfold LocFun.add. condtac; ss.
              eapply Time.join_spec; eauto.
              unfold TimeMap.bot. apply Time.bot_spec.
          }
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|] eqn:GET_PREV; ss.
          exploit FULFILL1; try exact GET_SRC. i. des.
          unfold prev_released_le_loc in PREV0. rewrite GET_PREV in *.
          inv TVIEW0. inv PREV0. econs; ss.
          * unfold LocFun.add. condtac; ss.
            eapply Time.join_spec; eauto.
          * unfold LocFun.add. condtac; ss.
            eapply Time.join_spec; eauto.
        + guardH o. guardH o0.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. exfalso.
            exploit Memory.split_get0; try exact x0. i. des.
            exploit Memory.get_ts; try exact GETP. i. des.
            { subst. inv x0. inv SPLIT. inv TS12. }
            exploit Memory.get_ts; try exact GET1. i. des.
            { subst. inv x0. inv SPLIT. inv TS23. }
            exploit Memory.get_disjoint; [exact GETP|exact GET1|..]. i. des.
            { subst. inv x0. inv SPLIT. timetac. }
            destruct (TimeFacts.le_lt_dec to0 ts3).
            { apply (x4 to0); econs; ss; try refl.
              inv x0. inv SPLIT. etrans; eauto. }
            { apply (x4 ts3); econs; ss; try refl.
              - inv x0. inv SPLIT. ss.
              - econs. ss. }
          * guardH o1. des. subst.
            exploit Memory.split_get0; try exact x1. i. des.
            unfold prev_released_le_loc in PREV.
            rewrite GET1 in *. ss.
    }

    { (* lower *)
      guardH RESERVE.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit COMPLETE; eauto. i. des. clear GET GET0.
      exploit (@Memory.lower_exists promises1_src loc from to msg_src
                                    (get_message_src false l loc msg_tgt tview_src from mem1_src)); eauto.
      { inv MEM. inv LOWER. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv LOWER. ss. }
      { unguard. des. subst.
        destruct released; cycle 1.
        - inv MSG_LE. inv RELEASED. inv MSG. inv RELEASED. ss. refl.
        - exploit Memory.lower_get0; try exact PROMISES. i. des.
          exploit SOUND; eauto. i. des.
          rewrite GET_TGT in *. inv GET. inv MSG. inv RELEASED.
          inv MSG_LE. inv RELEASED; [econs|]; ss.
          exploit FULFILL1; eauto. i. des.
          assert (BOT: View.le (get_released_src false l loc lhs tview_src View.bot) view_src).
          { inv SIM. inv TVIEW. econs; ss.
            - unfold TimeMap.bot.
              ii. unfold LocFun.add. condtac; ss.
              + subst. eapply Time.join_spec; eauto using Time.bot_spec.
              + exploit PLN; try eapply n. i. rewrite x. apply LE.
            - unfold TimeMap.bot.
              ii. unfold LocFun.add. condtac; ss.
              + subst. eapply Time.join_spec; eauto using Time.bot_spec.
              + exploit RLX; try eapply n. i. rewrite x. apply LE.
          }
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|] eqn:GET_PREV; econs; econs; ss.
          unfold prev_released_le_loc in PREV. rewrite GET_PREV in *.
          inv SIM. inv TVIEW. inv PREV. econs; ss.
          + ii. unfold LocFun.add. condtac; ss.
            * subst. eapply Time.join_spec; eauto.
            * exploit PLN; try eapply n. i. rewrite x. apply LE.
          + ii. unfold LocFun.add. condtac; ss.
            * subst. eapply Time.join_spec; eauto.
            * exploit RLX; try eapply n. i. rewrite x. apply LE.
      }
      i. des.
      exploit Memory.lower_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 3; eauto.
        + eapply get_message_src_message_to; eauto.
        + unguard. des. subst. inv MSG_LE. inv MSG. eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.lower_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.lower_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.lower_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND0; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.lower_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE0; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
      - ii. revert GETP. erewrite Memory.lower_o; eauto. condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.lower_o; eauto. condtac; ss. des. subst.
          inv x0. inv LOWER. timetac.
        + guardH o.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.lower_o; eauto. condtac; ss.
          des. subst.
          exploit Memory.lower_get0; try exact x1. i. des.
          unfold prev_released_le_loc in PREV. rewrite GET in *.
          inv x1. inv MSG_LE0; ss.
          * inv RELEASED; ss.
            unnw. etrans; try exact PREV.
            inv LE. econs; eauto.
          * exploit SOUND0; try exact GET; eauto. i. des. inv MSG0.
            exploit Memory.lower_get0; try exact MEM. i. des.
            rewrite GET1 in *. inv GET_TGT.
            unguardH RESERVE. des. ss.
    }

    { (* cancel *)
      exploit Memory.remove_get0; try exact PROMISES. i. des.
      exploit COMPLETE; eauto. i. des. inv MSG.
      exploit Memory.remove_exists; try exact GET_SRC. i. des.
      exploit Memory.remove_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 4; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit SOUND; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit COMPLETE; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit SOUND0; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit COMPLETE0; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
      - ii. revert GETP. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o.
        exploit FULFILL1; eauto. i. des. split; auto.
        unfold prev_released_le_loc in *.
        erewrite Memory.remove_o; eauto. condtac; ss.
    }
  Qed.

  Lemma promise_strong_relaxed
        l tview_src
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_memory l promises1_src promises1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (FULFILL1: fulfillable l tview_src mem1_src promises1_src)
        (TVIEW_SRC: TView.wf tview_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (KIND_TGT: negb (Memory.op_kind_is_lower kind_tgt) /\ negb (Memory.op_kind_is_cancel kind_tgt))
        (SPLIT_TGT: Memory.op_kind_is_split kind_tgt ->
                         (exists ts3 val, kind_tgt = Memory.op_kind_split ts3 (Message.full val None)) \/
                         (exists ts3, kind_tgt = Memory.op_kind_split ts3 Message.reserve))
        (LOC: loc <> l):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to
                                    (get_message_src true l loc msg_tgt tview_src from mem1_src)
                                    promises2_src mem2_src kind_src>> /\
      <<PROMISES2: sim_memory l promises2_src promises2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILL2: fulfillable l tview_src mem2_src promises2_src>>.
  Proof.
    des. inv PROMISES1. inv MEM1. inv PROMISE_TGT; ss.
    { (* add *)
      exploit (@Memory.add_exists mem1_src loc from to
                                  (get_message_src true l loc msg_tgt tview_src from mem1_src)).
      { ii. exploit SOUND0; eauto. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des.
        { subst. congr. }
        apply (x2 x); eauto. }
      { inv MEM. inv ADD. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv ADD. ss. }
      i. des.
      exploit Memory.add_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs; eauto.
        + eapply get_message_src_message_to; eauto.
        + i. exploit get_message_src_reserve; eauto. i. subst.
          exploit RESERVE; eauto. i. des.
          exploit COMPLETE0; try exact x; eauto. i. des.
          inv MSG. eauto.
        + i. exploit SOUND0; try exact GET; eauto. i. des.
          destruct msg_tgt; ss. eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - ii. revert GETP. erewrite Memory.add_o; eauto. condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss.
          des. subst. inv x0. inv ADD. timetac.
        + guardH o.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss. des. subst.
          destruct (get_message_src true l loc msg_tgt tview_src from mem1_src) eqn:GET; ss.
          exploit get_message_src_full; eauto. i. des. subst.
          exploit LE1_SRC; try exact GETP. i.
          exploit SOUND0; try exact x; eauto. i. des. inv MSG.
          exploit ATTACH; eauto; ss.
    }

    { (* split *)
      guardH RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      clear GET GET1 GET2.
      exploit COMPLETE; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3
                                    (get_message_src true l loc msg_tgt tview_src from mem1_src) msg_src); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv SPLIT. ss. }
      i. des.
      exploit Memory.split_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 2; eauto.
        + eapply get_message_src_message_to; eauto.
        + unguard. des. subst.
          unfold get_message_src.
          destruct released'; eauto.
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|]; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - ii. revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. inv x0. inv SPLIT. timetac.
          * guardH o. des. subst.
            inv x0. inv SPLIT. rewrite TS12 in TS23. timetac.
        + guardH o. des. subst. inv GETP.
          exploit LE1_SRC; eauto. i.
          exploit SOUND0; eauto. i. des. inv MSG0. inv RELEASED.
          exploit SPLIT_TGT; eauto. i. des.
          * inv x2. exploit LE1_TGT; eauto. i. congr.
          * inv x2. exploit LE1_TGT; eauto. i. congr.
        + guardH o. guardH o0.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. exfalso.
            exploit Memory.split_get0; try exact x0. i. des.
            exploit Memory.get_ts; try exact GETP. i. des.
            { subst. inv x0. inv SPLIT. inv TS12. }
            exploit Memory.get_ts; try exact GET1. i. des.
            { subst. inv x0. inv SPLIT. inv TS23. }
            exploit Memory.get_disjoint; [exact GETP|exact GET1|..]. i. des.
            { subst. inv x0. inv SPLIT. timetac. }
            destruct (TimeFacts.le_lt_dec to0 ts3).
            { apply (x4 to0); econs; ss; try refl.
              inv x0. inv SPLIT. etrans; eauto. }
            { apply (x4 ts3); econs; ss; try refl.
              - inv x0. inv SPLIT. ss.
              - econs. ss. }
          * guardH o1. des. subst.
            exploit Memory.split_get0; try exact x1. i. des.
            unfold prev_released_le_loc in PREV.
            rewrite GET1 in *. ss.
    }
  Qed.

  Lemma promise_loc
        l
        promises1_src mem1_src
        promises1_tgt mem1_tgt from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_memory l promises1_src promises1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt l from to msg_tgt promises2_tgt mem2_tgt kind_tgt):
    <<PROMISES2: sim_memory l promises1_src promises2_tgt>> /\
    <<MEM2: sim_memory l mem1_src mem2_tgt>>.
  Proof.
    inv PROMISES1. inv MEM1. inv PROMISE_TGT.
    { (* add *)
      splits.
      - econs; i.
        + erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
    }
    { (* split *)
      splits.
      - econs; i.
        + erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
    }
    { (* lower *)
      splits.
      - econs; i.
        + erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
    }
    { (* cancel *)
      splits.
      - econs; i.
        + erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
    }
  Qed.

  Lemma promise_eq_promises
        l
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc <> l):
    forall to, Memory.get l to promises1 = Memory.get l to promises2.
  Proof.
    i. inv PROMISE.
    - erewrite (@Memory.add_o promises2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.split_o promises2); eauto. repeat condtac; ss.
      { des. subst. ss. }
      { des; subst; ss. }
    - erewrite (@Memory.lower_o promises2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.remove_o promises2); eauto. condtac; ss. des. subst. ss.
  Qed.

  Lemma promise_eq_mem
        l
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc <> l):
    forall to, Memory.get l to mem1 = Memory.get l to mem2.
  Proof.
    i. inv PROMISE.
    - erewrite (@Memory.add_o mem2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.split_o mem2); eauto. repeat condtac; ss.
      { des. subst. ss. }
      { des; subst; ss. }
    - erewrite (@Memory.lower_o mem2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.remove_o mem2); eauto. condtac; ss. des. subst. ss.
  Qed.


  (* local steps *)

  Lemma promise_step
        l
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (LOC: loc <> l)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt):
    exists msg_src lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem2_src lc2_src.(Local.promises)>>.
  Proof.
    inv STEP_TGT.
    exploit promise; try exact PROMISE; try apply LC1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    esplits.
    - econs; eauto.
      eapply get_message_src_closed; eauto; try apply WF1_SRC. i.
      exploit Memory.promise_op; try exact PROMISE_SRC. i.
      eapply Memory.op_closed_view; eauto.
    - inv LC1. econs; eauto.
    - ss.
    - ss.
  Qed.

  Lemma promise_step_release
        l
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to val released_tgt lc2_tgt mem2_tgt kind_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (LOC: loc <> l)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to
                                      (Message.full val (Some (released_tgt))) lc2_tgt mem2_tgt kind_tgt)
        (KIND_TGT: negb (Memory.op_kind_is_lower kind_tgt) /\ negb (Memory.op_kind_is_cancel kind_tgt))
        (SPLIT_TGT: Memory.op_kind_is_split kind_tgt ->
                         (exists ts3 val, kind_tgt = Memory.op_kind_split ts3 (Message.full val None)) \/
                         (exists ts3, kind_tgt = Memory.op_kind_split ts3 Message.reserve)):
    exists released_src lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to
                                     (Message.full val (Some (released_src))) lc2_src mem2_src kind_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem2_src lc2_src.(Local.promises)>> /\
      <<STRONG: view_le_loc l lc1_src.(Local.tview).(TView.cur) released_src>>.
  Proof.
    inv STEP_TGT.
    exploit promise_strong_relaxed; try exact PROMISE; try apply LC1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    exploit (@get_message_src_closed true l loc (Message.full val (Some released_tgt))
                                     lc1_src.(Local.tview) from mem1_src mem2_src mem2_tgt); eauto.
    { apply WF1_SRC. }
    { exploit Memory.promise_op; try exact PROMISE_SRC. i.
      eapply Memory.op_closed_view; eauto. }
    i. ss.
    destruct (Memory.get loc from mem1_src) as [[? [? []|]]|]; ss.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
  Qed.

  Lemma read_step
        l
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (LOC: loc <> l)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt):
    exists released_src lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released_src ord lc2_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem1_src lc2_src.(Local.promises)>>.
  Proof.
    inv STEP_TGT.
    inv MEM1. exploit COMPLETE; eauto. i. des. inv MSG.
    esplits.
    - econs; eauto.
      admit.
    - admit.
    - ss.
  Admitted.

  Lemma fulfill_step_relaxed
        l
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (REL: sim_opt_view l releasedm_src releasedm_tgt)
        (REL_WF: View.opt_wf releasedm_src)
        (REL_GET: __guard__ (
                      Time.le (releasedm_src.(View.unwrap).(View.rlx) loc) to /\
                      (releasedm_src = None \/
                       exists from' val',
                         Memory.get loc from mem1_src = Some (from', Message.full val' releasedm_src))))
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (LOC: loc <> l)
        (ORD: Ordering.le ord Ordering.strong_relaxed)
        (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt):
    exists released_src promises2_src mem2_src,
      <<WRITE_SRC: Memory.write lc1_src.(Local.promises) mem1_src loc from to
                                val (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord)
                                promises2_src mem2_src
                                (Memory.op_kind_lower (Message.full val released_src))>> /\
      <<PROMISES2: sim_memory l promises2_src lc2_tgt.(Local.promises)>> /\
      <<MEM2: sim_memory l mem2_src mem1_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit Memory.remove_get0; eauto. i. des.
    destruct lc1_src as [tview1_src promises1_src]. ss.
    dup LC1. inv LC0. inv PROMISES1. ss.
    exploit COMPLETE; eauto. i. des. inv MSG.
    clear TVIEW SOUND COMPLETE.
    exploit (@Memory.lower_exists promises1_src loc from to
                                  (Message.full val released_src)
                                  (Message.full val (TView.write_released tview1_src sc1_src loc to releasedm_src ord))); ss.
    { econs.
      eapply TViewFacts.write_future0; try eapply WF1_SRC; eauto. }
    { econs. destruct released_src; ss.
      - revert REL_LE. unfold TView.write_released.
        condtac; ss. repeat condtac; ss; i.
        { destruct ord; ss. }
        inv REL_LE. econs.
        exploit View.join_l. i. erewrite LE in x0.
        exploit View.join_r. i. erewrite LE in x1.
        clear LE. eapply View.join_spec.
        + unguard. des; subst; eauto using View.bot_spec.
          inv REL; eauto using View.bot_spec. inv SIM.
          inv RELEASED. inv SIM. inv x0. ss.
          exploit FULFILLABLE1; eauto. i. des.
          unfold prev_released_le_loc in *.
          rewrite REL_GET0 in PREV. inv PREV.
          econs; ii.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit PLN; eauto. i.
            exploit PLN0; eauto. i.
            rewrite x. rewrite x0. ss.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit RLX; eauto. i.
            exploit RLX0; eauto. i.
            rewrite x. rewrite x0. ss.
        + revert x1. unfold LocFun.add. condtac; ss. i.
          inv RELEASED. inv SIM. inv LC1. inv TVIEW. destruct (REL0 loc). ss.
          exploit View.join_l. i. erewrite x1 in x2.
          exploit View.join_r. i. erewrite x1 in x3.
          inv x2. inv x3. ss.
          exploit FULFILLABLE1; eauto. i. des. inv TVIEW.
          eapply View.join_spec.
          { econs; ii.
            - destruct (Loc.eq_dec loc0 l); subst; ss.
              exploit PLN; eauto. i.
              exploit PLN0; eauto. i.
              rewrite x. rewrite x2. ss.
            - destruct (Loc.eq_dec loc0 l); subst; ss.
              exploit RLX; eauto. i.
              exploit RLX0; eauto. i.
              rewrite x. rewrite x2. ss. }
          { econs; ss; ii.
            - specialize (PLN2 loc0). revert PLN2.
              unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
              + subst. exploit PLN; eauto. i. rewrite x. ss.
              + unfold LocFun.find, LocFun.init. apply Time.bot_spec.
            - specialize (RLX2 loc0). revert RLX2.
              unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
              + subst. exploit RLX; eauto. i. rewrite x. ss.
              + unfold LocFun.find, LocFun.init. apply Time.bot_spec. }
      - inv RELEASED. inv REL_LE.
        revert H0. unfold TView.write_released. condtac; ss. }
    i. des.
    exploit Memory.lower_get0; try exact x0. i. des.
    exploit Memory.remove_exists; try exact GET2. i. des.
    exploit Memory.lower_exists_le; try eapply WF1_SRC; eauto. i. des.
    esplits.
    - econs; eauto; ss. econs 3; eauto.
      econs. unfold TView.write_released.
      repeat (condtac; ss); try by (destruct ord; ss).
      + unfold TimeMap.join.
        unfold LocFun.add. condtac; ss.
        unfold TimeMap.join.
        unfold TimeMap.singleton, LocFun.add. condtac; ss.
        eapply Time.join_spec.
        * unguard. des; ss.
        * eapply Time.join_spec; try refl.
          inv LC1. inv TVIEW. destruct (REL0 loc). ss.
          exploit RLX; eauto. i. rewrite x.
          inv WRITABLE. etrans; [|econs; eauto].
          inv WF1_TGT. inv TVIEW_WF. destruct (REL_CUR loc). ss.
      + unfold TimeMap.bot. apply Time.bot_spec.
    - admit.
    - admit.
  Admitted.

  Lemma fulfill_step_release
        l
        lc1_src sc1_src mem1_src releasedm_src val released_src
        lc1_tgt sc1_tgt mem1_tgt loc from to releasedm_tgt released_tgt ord lc2_tgt sc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (REL: sim_opt_view l releasedm_src releasedm_tgt)
        (REL_WF: View.opt_wf releasedm_src)
        (REL_GET: __guard__ (
                      Time.le (releasedm_src.(View.unwrap).(View.rlx) loc) to /\
                      (releasedm_src = None \/
                       exists from' val',
                         Memory.get loc from mem1_src = Some (from', Message.full val' releasedm_src))))
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (GET_SRC: Memory.get loc to lc1_src.(Local.promises) = Some (from, Message.full val (Some released_src)))
        (STRONG: view_le_loc l lc1_src.(Local.tview).(TView.cur) released_src)
        (LOC: loc <> l)
        (ORD: Ordering.le Ordering.acqrel ord)
        (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt):
    exists released_src promises2_src mem2_src,
      <<WRITE_SRC: Memory.write lc1_src.(Local.promises) mem1_src loc from to
                                val (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord)
                                promises2_src mem2_src
                                (Memory.op_kind_lower (Message.full val (Some released_src)))>> /\
      <<PROMISES2: sim_memory l promises2_src lc2_tgt.(Local.promises)>> /\
      <<MEM2: sim_memory l mem2_src mem1_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit Memory.remove_get0; eauto. i. des.
    destruct lc1_src as [tview1_src promises1_src]. ss.
    dup LC1. inv LC0. inv PROMISES1. ss.
    exploit COMPLETE; eauto. i. des.
    rewrite GET_SRC in *. inv GET_SRC0. inv MSG. inv RELEASED.
    clear TVIEW SOUND COMPLETE.
    exploit (@Memory.lower_exists promises1_src loc from to
                                  (Message.full val (Some released_src))
                                  (Message.full val (TView.write_released tview1_src sc1_src loc to releasedm_src ord))); ss.
    { econs.
      eapply TViewFacts.write_future0; try eapply WF1_SRC; eauto. }
    { econs.
      revert REL_LE. unfold TView.write_released.
      condtac; try by (destruct ord; ss). ss.
      repeat condtac; ss. i.
      inv REL_LE. econs.
      exploit View.join_l. i. erewrite LE in x0.
      exploit View.join_r. i. erewrite LE in x1.
      clear LE. eapply View.join_spec.
      - unguard. des; subst; eauto using View.bot_spec.
        inv REL; eauto using View.bot_spec. inv SIM.
        inv SIM0. inv x0. ss.
        exploit FULFILLABLE1; eauto. i. des.
        unfold prev_released_le_loc in *.
        rewrite REL_GET0 in PREV. inv PREV.
        econs; ii.
        + destruct (Loc.eq_dec loc0 l); subst; ss.
          exploit PLN; eauto. i.
          exploit PLN0; eauto. i.
          rewrite x. rewrite x0. ss.
        + destruct (Loc.eq_dec loc0 l); subst; ss.
          exploit RLX; eauto. i.
          exploit RLX0; eauto. i.
          rewrite x. rewrite x0. ss.
      - revert x1. unfold LocFun.add. condtac; ss. i.
        inv SIM. inv LC1. inv TVIEW. inv CUR. inv STRONG. ss.
        exploit View.join_l. i. erewrite x1 in x2.
        exploit View.join_r. i. erewrite x1 in x3.
        inv x2. inv x3. ss.
        exploit FULFILLABLE1; eauto. i. des. inv TVIEW.
        eapply View.join_spec.
        + econs; ii.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit PLN; eauto. i.
            exploit PLN0; eauto. i.
            rewrite x. rewrite x2. ss.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit RLX; eauto. i.
            exploit RLX0; eauto. i.
            rewrite x. rewrite x2. ss.
        + econs; ss; ii.
          * specialize (PLN2 loc0). revert PLN2.
            unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
            { subst. exploit PLN; eauto. i. rewrite x. ss. }
            { unfold LocFun.find, LocFun.init. apply Time.bot_spec. }
          * specialize (RLX2 loc0). revert RLX2.
            unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
            { subst. exploit RLX; eauto. i. rewrite x. ss. }
            { unfold LocFun.find, LocFun.init. apply Time.bot_spec. }
    }
    i. des.
    exploit Memory.lower_get0; try exact x0. i. des.
    exploit Memory.remove_exists; try exact GET2. i. des.
    exploit Memory.lower_exists_le; try eapply WF1_SRC; eauto. i. des.
    esplits.
    - econs; eauto; ss. econs 3; eauto.
      econs. unfold TView.write_released.
      repeat (condtac; ss; try by (destruct ord; ss)).
      unfold TimeMap.join.
      unfold LocFun.add. condtac; ss.
      unfold TimeMap.join.
      unfold TimeMap.singleton, LocFun.add. condtac; ss.
      eapply Time.join_spec.
      + unguard. des; ss.
      + eapply Time.join_spec; try refl.
        inv LC1. inv TVIEW. inv CUR. ss.
        exploit RLX; eauto. i. rewrite x.
        inv WRITABLE. etrans; [|econs; eauto]. refl.
    - admit.
    - admit.
  Admitted.

  Lemma write_step
        l
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt
                                    ord lc2_tgt sc2_tgt mem2_tgt kind_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (SC1: sim_timemap l sc1_src sc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (RELEASED: sim_opt_view l releasedm_src releasedm_tgt)
        (REL_WF_SRC: View.opt_wf releasedm_src)
        (REL_CLOSED_SRC: Memory.closed_opt_view releasedm_src mem1_src)
        (REL_WF_TGT: View.opt_wf releasedm_tgt)
        (REL_CLOSED_TGT: Memory.closed_opt_view releasedm_tgt mem1_tgt)
        (REL_GET: __guard__ (
                      Time.le (releasedm_src.(View.unwrap).(View.rlx) loc) to /\
                      (releasedm_src = None \/
                       exists from' val',
                         Memory.get loc from mem1_src = Some (from', Message.full val' releasedm_src))))
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (LOC: loc <> l)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt
                                    ord lc2_tgt sc2_tgt mem2_tgt kind_tgt):
    exists released_src lc2_src sc2_src mem2_src kind_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src
                                    ord lc2_src sc2_src mem2_src kind_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<SC2: sim_timemap l sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem1_src lc2_src.(Local.promises)>>.
  Proof.
    destruct (Ordering.le ord Ordering.strong_relaxed) eqn:ORD.
    { (* relaxed *)
      exploit write_promise_fulfill; eauto. i. des.
      exploit promise_step; try exact STEP1; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
      exploit fulfill_step_relaxed; try exact STEP2; eauto.
      { unguard. des; eauto. split; auto. right.
        inv STEP_SRC. inv PROMISE.
        - erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv ADD. timetac.
        - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          + des. subst. inv MEM. inv SPLIT. timetac.
          + guardH o. des. subst.
            inv MEM. inv SPLIT. rewrite TS12 in TS23. timetac.
        - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv LOWER. timetac.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. exploit Memory.remove_get0; try exact MEM. i. des. congr. }
      i. des.
      inv STEP_SRC; ss.
      replace msg_src with (Message.full val released_src) in *; cycle 1.
      { inv WRITE_SRC. inv PROMISE0.
        exploit Memory.lower_get0; try exact MEM. i. des.
        exploit Memory.promise_get2; try exact PROMISE.
        { destruct kind_src; ss. inv PROMISE.
          exploit Memory.remove_get0; try exact MEM3. i. des. congr. }
        i. des.
        rewrite GET in *. inv GET_MEM. ss. }
      exploit MemoryMerge.promise_write_write; try exact PROMISE; eauto. i.
      esplits.
      - econs; eauto.
        + admit.
        + admit.
      - econs; ss.
        admit.
      - by inv STEP_TGT.
      - ss.
      - admit.
    }
    { (* release *)
      destruct released_tgt as [released_tgt|]; cycle 1.
      { inv STEP_TGT. revert RELEASED0.
        unfold TView.write_released. condtac; ss.
        destruct ord; ss. }
      exploit write_promise_fulfill; eauto. i. des.
      exploit promise_step_release; try exact STEP1; eauto.
      { exploit Local.write_step_strong_relaxed; eauto; try by destruct ord. i.
        exploit Local.write_step_non_cancel; eauto. }
      { i. destruct kind_tgt; ss. inv STEP_TGT.
        hexploit RELEASE; try by destruct ord. i.
        destruct msg3 as [? []|]; eauto.
        inv WRITE. inv PROMISE.
        exploit Memory.split_get0; try exact PROMISES. i. des.
        exploit H0; eauto; ss. }
      i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
      dup STEP_SRC. inv STEP_SRC0. clear CLOSED.
      exploit Memory.promise_get2; try exact PROMISE; try by inv PROMISE. i. des.
      exploit fulfill_step_release; try exact STEP2; eauto.
      { unguard. des; eauto. split; auto. right.
        inv STEP_SRC. inv PROMISE.
        - erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv ADD. timetac.
        - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          + des. subst. inv MEM. inv SPLIT. timetac.
          + guardH o. des. subst.
            inv MEM. inv SPLIT. rewrite TS12 in TS23. timetac.
        - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv LOWER. timetac.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto. }
      { destruct ord; ss. }
      i. des.
      replace released_src0 with released_src in *; cycle 1.
      { inv WRITE_SRC. inv PROMISE0.
        exploit Memory.lower_get0; try exact MEM. i. des.
        rewrite GET in *. inv GET_MEM. ss. }
      exploit MemoryMerge.promise_write_write; try exact PROMISE; eauto. i.
      esplits.
      - econs; eauto.
        + admit.
        + admit.
      - econs; ss.
        admit.
      - by inv STEP_TGT.
      - ss.
      - admit.
    }
  Admitted.

  Lemma fence_step
        l
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt ordr ordw lc2_tgt sc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (SC1: sim_timemap l sc1_src sc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (PROMISES1: forall to, Memory.get l to lc1_src.(Local.promises) = None)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr ordw lc2_tgt sc2_tgt):
    exists lc2_src sc2_src,
      <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr ordw lc2_src sc2_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<SC2: sim_timemap l sc2_src sc2_tgt>> /\
      <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem1_src lc2_src.(Local.promises)>>.
  Proof.
    inv STEP_TGT. esplits.
    - econs; eauto. ii.
      hexploit RELEASE; eauto.
      inv LC1. inv PROMISES0. exploit SOUND; eauto.
      { ii. subst. congr. }
      i. des. inv MSG; ss.
      exploit H0; eauto. i. inv RELEASED; ss.
    - admit.
    - admit.
    - unfold TView.write_fence_tview. repeat condtac; ss; ii.
      + destruct ordw; ss.
        inv LC1. inv PROMISES0. exploit SOUND; eauto.
        { ii. subst. congr. }
        i. des. inv MSG. inv RELEASED.
        exploit RELEASE; eauto. ss.
      + destruct ordw; ss.
        inv LC1. inv PROMISES0. exploit SOUND; eauto.
        { ii. subst. congr. }
        i. des. inv MSG. inv RELEASED.
        exploit RELEASE; eauto. ss.
  Admitted.

  Lemma failure_step
        l
        lc1_src
        lc1_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (PROMISES1: forall to, Memory.get l to lc1_src.(Local.promises) = None)
        (STEP_TGT: Local.failure_step lc1_tgt):
    <<STEP_SRC: Local.failure_step lc1_src>>.
  Proof.
    inv STEP_TGT. econs. ii.
    assert (LOC: loc <> l) by (ii; subst; congr).
    inv LC1. inv PROMISES0.
    exploit SOUND; eauto. i. des. inv MSG.
    exploit CONSISTENT; eauto. i.
    inv TVIEW. inv CUR. exploit RLX; eauto. i.
    rewrite x0. ss.
  Qed.

  Definition is_accessing_loc (l: Loc.t) (e: ThreadEvent.t): Prop :=
    match ThreadEvent.is_accessing e with
    | Some (loc, _) => loc <> l
    | None => True
    end.

  Lemma program_step
        l
        lc1_src sc1_src mem1_src
        e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (SC1: sim_timemap l sc1_src sc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (PROMISES1: forall to, Memory.get l to lc1_src.(Local.promises) = None)
        (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
        (LOC: is_accessing_loc l e_tgt)
        (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt):
    exists e_src lc2_src sc2_src mem2_src,
      <<STEP_SRC: Local.program_step e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<SC2: sim_timemap l sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem1_src lc2_src.(Local.promises)>>.
  Proof.
    unfold is_accessing_loc in *.
    inv STEP_TGT; ss.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; [econs 2|..]; eauto.
    - hexploit write_step; eauto.
      { admit. }
      i. des.
      esplits; [econs 3|..]; eauto.
    - exploit read_step; eauto. i. des.
      exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      hexploit write_step; try exact LOCAL2; eauto.
      { admit. }
      { admit. }
      i. des.
      esplits; [econs 4|..]; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; [econs 5|..]; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; [econs 6|..]; eauto. refl.
    - exploit failure_step; eauto. i. des.
      esplits; [econs 7|..]; eauto.
  Admitted.
End SimCommon.
