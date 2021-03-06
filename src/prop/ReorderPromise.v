From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import MemoryReorder.
Require Import PromiseConsistent.
Require Import FulfillStep.

Set Implicit Arguments.


Lemma reorder_promise_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1 kind1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: (loc1, to1) <> (loc2, to2)):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get_inv_diff; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_promise_promise_lower_None
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 (Message.concrete val2 None) lc2 mem2 kind2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (KIND2: Memory.op_kind_is_lower kind2 = true):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ Message.le (Message.concrete val2 None) msg1 /\ kind2 = Memory.op_kind_lower msg1 /\
   exists kind1', <<STEP: Local.promise_step lc0 mem0 loc1 from1 to1 (Message.concrete val2 None) lc2 mem2 kind1'>>) \/
  (exists lc1' mem1' from2' kind1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2' to2 (Message.concrete val2 None) lc1' mem1' kind2>> /\
      <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 msg1 lc2 mem2 kind1'>>).
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE0; inv KIND2. des. subst.
  inv PROMISE; ss.
  - exploit MemoryReorder.add_lower; try exact PROMISES0; try exact PROMISES; eauto. i. des.
    + subst.
      exploit MemoryReorder.add_lower; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
      left. esplits; ss.
      * inv MEM. inv LOWER. ss.
      * econs; eauto. econs; eauto.
        i. inv MEM. inv LOWER. inv MSG_LE; ss; eauto.
        eapply ATTACH; eauto. ss.
    + exploit MemoryReorder.add_lower; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
      right. esplits; eauto; econs; eauto.
      * econs; eauto.
        i. revert GET.
        erewrite Memory.lower_o; eauto. condtac; ss.
        { i. des. subst. inv GET.
          exploit Memory.lower_get0; try exact MEM. i. des.
          revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv LOWER. timetac. }
        { i. exploit Memory.lower_get1; try exact GET; eauto. }
      * eapply Memory.lower_closed_message; eauto.
  - des. subst.
    destruct (classic ((loc1, ts3) = (loc2, to2))).
    { inv H.
      exploit MemoryReorder.split_lower_same; try exact PROMISES0; try exact PROMISES; eauto. i. des.
      exploit MemoryReorder.split_lower_same; try exact MEM1; try exact MEM; eauto. i. des.
      subst. right. esplits; eauto; econs; eauto.
      eapply Memory.lower_closed_message; eauto.
    }
    { exploit MemoryReorder.split_lower_diff; try exact PROMISES0; try exact PROMISES; eauto. i. des.
      - subst.
        exploit MemoryReorder.split_lower_diff; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
        left. esplits; eauto. inv MEM. inv LOWER. ss.
      - exploit MemoryReorder.split_lower_diff; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
        right. esplits; eauto; econs; eauto.
        eapply Memory.lower_closed_message; eauto.
    }
  - des. subst.
    exploit MemoryReorder.lower_lower; try exact PROMISES0; try exact PROMISES; eauto. i. des.
    + subst.
      exploit MemoryReorder.lower_lower; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
      left. esplits; eauto. inv MEM. inv LOWER. ss.
    + exploit MemoryReorder.lower_lower; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
      right. esplits; eauto; econs; eauto.
      eapply Memory.lower_closed_message; cycle 1; eauto.
Qed.

Lemma reorder_promise_promise_cancel
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (KIND2: Memory.op_kind_is_cancel kind2 = true):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg1 = Message.reserve /\ kind1 = Memory.op_kind_add /\
   lc0 = lc2 /\ mem0 = mem2) \/
  (exists lc1' mem1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2>> /\
      <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 msg1 lc2 mem2 kind1>>).
Proof.
  inv STEP1. inv STEP2. ss. destruct kind2; ss.
  exploit MemoryReorder.promise_cancel; try exact PROMISE; eauto. i. des.
  - left. splits; auto. destruct lc0; ss. subst. ss.
  - right. esplits.
    + econs; eauto.
      inv CANCEL1. eapply Memory.cancel_closed_message; eauto.
    + econs; eauto.
      inv PROMISE0. eapply Memory.cancel_closed_message; eauto.
Qed.

Lemma reorder_promise_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (REL_CLOSED: forall promises1' mem1' kind1'
                     (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 msg2 promises1' mem1' kind1'),
          Memory.closed_message msg2 mem1')
      (LOCAL0: Local.wf lc0 mem0)
      (CLOSED0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (MSG2: msg2 <> Message.reserve)
      (LOCTS1: forall to1' msg1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2 /\
          (forall msg2', kind2 <> Memory.op_kind_split to1' msg2'))
      (LOCTS2: forall (LOC: loc1 = loc2)
                 (KIND1: kind1 = Memory.op_kind_add)
                 (KIND2: kind2 = Memory.op_kind_add)
                 (MSG1: msg1 <> Message.reserve),
               Time.lt to2 to1):
  exists lc1' mem1' kind2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                (exists from1' kind1',
                    (loc1, to1) <> (loc2, to2) /\
                    (forall to1' msg1'
                       (LOC: loc1 = loc2)
                       (KIND: kind1' = Memory.op_kind_split to1' msg1'),
                        to1' <> to2 /\
                        (forall msg2', kind2 <> Memory.op_kind_split to1' msg2')) /\
                    Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1' /\
                    Memory.op_kind_is_cancel kind1' = false /\
                    (Memory.op_kind_is_lower kind1 = false -> Memory.op_kind_is_lower kind1' = false))
               )>> /\
    <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE; ss.
  { inv PROMISE0; ss.
    - (* add/add *)
      exploit MemoryReorder.add_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 msg2
                            mem1' mem1'0 Memory.op_kind_add).
        { i. econs; eauto. }
        econs; eauto; try congr.
        i. exploit Memory.add_get1; try exact MEM; eauto.
      + right. esplits; eauto. econs; eauto.
        * econs; eauto. i. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; eauto.
          i. des. inv GET.
          exploit LOCTS2; eauto. intros x.
          inv ADD0. inv ADD. rewrite x in TO. timetac.
        * eapply Memory.add_closed_message; cycle 1; eauto.
      + auto.
    - (* add/split *)
      exploit MemoryReorder.add_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 msg2
                              mem1' mem1'0 Memory.op_kind_add).
          { i. econs; eauto. }
          econs; eauto; try congr.
          i. exploit Memory.add_get1; try exact GET; try exact MEM. i.
          exploit Memory.add_get0; try exact MEM. i. des.
          clear GET GET0.
          exploit Memory.get_ts; try exact x4. i. des.
          { subst. inv ADD0. inv ADD. inv TO. }
          exploit Memory.get_ts; try exact GET1. i. des.
          { subst. inv ADD3. inv ADD. inv TO. }
          exploit Memory.get_disjoint; [exact x4|exact GET1|..]. i. des.
          { subst. inv ADD0. inv ADD. timetac. }
          destruct (TimeFacts.le_lt_dec to' ts3).
          { apply (x7 to'); econs; ss; try refl.
            inv ADD0. inv ADD. etrans; eauto. }
          { apply (x7 ts3); econs; ss; try refl.
            - inv ADD3. inv ADD. ss.
            - econs. ss. }
        * right. esplits; eauto.
          { ii. inv H. inv ADD3. inv ADD. timetac. }
          { econs.
            - econs; eauto.
              i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss; eauto. i. des. inv GET.
              inv ADD0. inv ADD. inv ADD3. inv ADD. rewrite TO in TO0. timetac.
            - eapply Memory.split_closed_message; eauto.
            - auto. }
        * auto.
      + exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.split_get0; try exact MEM0; eauto. i. des.
            revert GET. erewrite Memory.add_o; eauto. condtac; ss. des; congr. }
          { econs; eauto.
            - econs; eauto.
              i. revert GET.
              erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
              + i. des. inv GET.
                exploit Memory.split_get0; try exact MEM0. i. des.
                revert GET0. erewrite Memory.add_o; eauto. condtac; ss; eauto.
                i. des. inv GET0.
                inv MEM0. inv SPLIT. rewrite TS12 in TS23. timetac.
              + guardH o. i. des. inv GET.
                exploit Memory.split_get0; try exact SPLIT0. i. des.
                exploit Memory.add_get0; try exact ADD0. i. des.
                exploit Memory.add_get1; try exact GET1; eauto. i.
                clear GET GET0 GET1 GET2 GET3.
                exploit Memory.get_ts; try exact GET4. i. des.
                { subst. inv SPLIT0. inv SPLIT. inv TS12. }
                exploit Memory.get_ts; try exact x0. i. des.
                { subst. inv ADD0. inv ADD. inv TO. }
                exploit Memory.get_disjoint; [exact GET4|exact x0|..]. i. des.
                { subst. exploit Memory.split_get0; try exact SPLIT0. i. des.
                  inv ADD0. inv ADD.
                  hexploit DISJOINT; try eapply GET1. i.
                  apply (H to1); econs; ss; try refl. }
                apply (x3 to1); econs; ss; try refl.
            - eapply Memory.split_closed_message; eauto. }
        * auto.
    - (* add/lower *)
      des. subst.
      exploit MemoryReorder.add_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto. econs; eauto.
          i. inv MEM0. inv LOWER. inv MSG_LE; ss; eauto.
          eapply ATTACH; eauto. ss.
        * left. auto.
        * auto.
      + exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto. econs; eauto.
          { econs; eauto.
            i. revert GET.
            erewrite Memory.lower_o; eauto. condtac; ss; eauto.
            i. des. inv GET.
            exploit Memory.lower_get0; try exact LOWER0. i. des. eauto. }
          { eapply Memory.lower_closed_message; eauto. }
        * auto.
  }

  { des. subst. inv PROMISE0; ss.
    - (* split/add *)
      exploit MemoryReorder.split_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.split_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 msg2
                            mem1' mem1'0 Memory.op_kind_add).
        { i. econs; eauto. }
        econs; eauto; try congr.
        i. exploit Memory.split_get1; try exact GET; eauto. i. des.
        dup GET2. revert GET2.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
        * i. des. inv GET2.
          exploit Memory.split_get0; try exact MEM. i. des.
          rewrite GET in *. ss.
        * guardH o. i. des. inv GET2.
          exploit Memory.split_get0; try exact MEM. i. des.
          rewrite GET in *. inv GET2. eauto.
        * i. rewrite GET in *. inv GET2. eauto.
      + right. esplits; eauto. econs; eauto.
        eapply Memory.add_closed_message; eauto.
      + auto.
    - (* split/split *)
      des.
      exploit MemoryReorder.split_split; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. eapply LOCTS1; eauto. }
      i. des.
      + subst. exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. inv SPLIT2. inv SPLIT. timetac. }
        i. des; [|congr].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. inv SPLIT2. inv SPLIT. timetac. }
          { econs; eauto.
            eapply Memory.split_closed_message; cycle 1; eauto. }
        * congr.
      + exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. eapply LOCTS1; eauto. }
        i. des; [congr|].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
            revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
            guardH o0. des; congr. }
          { econs; eauto.
            eapply Memory.split_closed_message; cycle 1; eauto. }
        * auto.
    - (* split/lower *)
      des. subst.
      exploit MemoryReorder.split_lower_diff; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. exploit LOCTS1; eauto. i. des. congr. }
      i. des.
      + subst.
        exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS1; eauto. i. des. congr. }
        i. des; [|congr].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * left. auto.
        * congr.
      + subst. exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS1; eauto. i. des. congr. }
        i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto. econs; eauto.
          eapply Memory.lower_closed_message; eauto.
        * congr.
  }

  { des. subst. inv PROMISE0; ss.
    - (* lower/add *)
      exploit MemoryReorder.lower_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + cut (Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 msg2
                            mem1' mem1'0 Memory.op_kind_add).
        { i. econs; eauto. }
        econs; eauto; try congr.
        i. exploit Memory.lower_get1; try exact GET; eauto. i. des. eauto.
      + right. esplits; eauto. econs; eauto.
        eapply Memory.add_closed_message; eauto.
      + auto.
    - (* lower/split *)
      des.
      exploit MemoryReorder.lower_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_split; try exact MEM; try exact MEM0; eauto. i. des.
      unguardH FROM1. des.
      + inv FROM1. unguardH FROM0. des; [|congr]. inv FROM0.
        esplits.
        * econs.
          { econs 2; eauto. inv LOWER0. inv LOWER. inv MSG_LE; ss. }
          { eapply REL_CLOSED. econs 2; eauto.
            inv LOWER0. inv LOWER. inv MSG_LE; ss. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. inv SPLIT1. inv SPLIT. timetac. }
          { econs; eauto. eapply Memory.split_closed_message; eauto. }
        * congr.
      + inv FROM2. unguardH FROM0. des; [congr|]. inv FROM2.
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
          { auto. }
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.lower_get0; try exact MEM; eauto.
            exploit Memory.split_get0; try exact SPLIT0; eauto. i. des. congr. }
          { econs; eauto. eapply Memory.split_closed_message; eauto. }
        * auto.
    - (* lower/lower *)
      des. subst.
      exploit MemoryReorder.lower_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto.
        * left. auto.
        * congr.
      + exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto. econs; eauto.
          eapply Memory.lower_closed_message; cycle 1; eauto.
        * auto.
  }
Qed.

Lemma reorder_promise_fulfill
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS1: (loc1, to1) <> (loc2, to2))
      (LOCTS2: forall to1' msg1'
                 (LOC: loc1 = loc2)
                 (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE; ss.
  - exploit MemoryReorder.add_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
  - exploit MemoryReorder.split_remove; try exact PROMISES; try exact REMOVE; eauto.
    { ii. inv H. eapply LOCTS2; eauto. }
    i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss; eauto.
  - des. subst.
    exploit MemoryReorder.lower_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; eauto.
  - exploit MemoryReorder.remove_remove; try exact PROMISES; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
Qed.

Lemma promise_step_nonsynch_loc_inv
      lc1 mem1 loc from to msg lc2 mem2 kind l
      (WF1: Local.wf lc1 mem1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (NONPF: Memory.op_kind_is_lower kind = false \/ ~ Message.is_released_none msg)
      (NONSYNCH: Memory.nonsynch_loc l lc2.(Local.promises)):
  Memory.nonsynch_loc l lc1.(Local.promises).
Proof.
  guardH NONPF.
  ii. inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.split_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.lower_o; try exact PROMISES; eauto.
    instantiate (1 := t). instantiate (1 := l). condtac; ss.
    + i. des. subst. exploit NONSYNCH; eauto.
      destruct msg; destruct msg0; ss.
      * i. subst. unguard. des; ss.
      * exploit Memory.lower_get0; try exact PROMISES. i. des.
        rewrite GET0 in *. inv GET. inv MSG_LE.
    + rewrite GET. i. exploit NONSYNCH; eauto.
  - exploit Memory.remove_get1; try exact GET; eauto. i. des.
    + subst. exploit Memory.remove_get0; try exact PROMISES. i. des.
      rewrite GET0 in GET. inv GET. ss.
    + exploit NONSYNCH; eauto.
Qed.

Lemma reorder_promise_write_aux
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (NONPF: Memory.op_kind_is_lower kind1 = false \/ ~ Message.is_released_none msg1)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (LOCTS1: forall to1' msg1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2 /\
          (forall msg2', kind2 <> Memory.op_kind_split to1' msg2'))
      (LOCTS2: forall (LOC: loc1 = loc2)
                 (KIND1: kind1 = Memory.op_kind_add)
                 (KIND2: kind2 = Memory.op_kind_add)
                 (MSG1: msg1 <> Message.reserve),
               Time.lt to2 to1):
  exists kind2' lc1' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                ((loc1, to1) <> (loc2, to2) /\
                 exists from1' kind1',
                   <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>> /\
    <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>.
Proof.
  guardH NONPF.
  exploit Local.promise_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto; try by viewtac. i. des.
  exploit reorder_promise_promise; try exact STEP1; eauto; ss.
  { i. subst.
    exploit Memory.promise_op; eauto. i.
    econs. eapply TViewFacts.op_closed_released; try exact x0; eauto.
    inv STEP1. apply LOCAL0.
  }
  i. des.
  unguardH STEP5. des.
  - inv STEP5.
    exploit promise_fulfill_write; try exact STEP4; eauto.
    { i. hexploit ORD; eauto. i.
      eapply promise_step_nonsynch_loc_inv; try exact STEP1; eauto.
    }
    { inv STEP1. ss. }
    i. esplits; eauto. left; eauto.
  - exploit Local.promise_step_future; try exact STEP4; eauto. i. des.
    exploit reorder_promise_fulfill; try exact STEP6; eauto.
    { i. eapply STEP6; eauto. }
    i. des.
    exploit fulfill_step_future; try exact STEP7; try exact WF0; eauto; try by viewtac. i. des.
    exploit promise_fulfill_write; try exact STEP4; eauto; try by viewtac.
    { i. hexploit ORD; eauto. i.
      eapply promise_step_nonsynch_loc_inv; try exact STEP1; eauto.
    }
    { subst. inv STEP1. ss. }
    i. esplits; eauto. right. esplits; eauto.
Qed.

Lemma reorder_promise_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (NONPF: Memory.op_kind_is_lower kind1 = false \/ ~ Message.is_released_none msg1)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (CONS: Local.promise_consistent lc2):
  (exists kind2' lc1' mem1',
     <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
     <<STEP2: __guard__
                ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                 ((loc1, to1) <> (loc2, to2) /\
                  exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>> /\
     <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>).
Proof.
  guardH NONPF. eapply reorder_promise_write_aux; eauto.
  { i. subst. split.
    - ii. subst. ss. inv STEP1.
      exploit Memory.promise_get2; eauto. i. des. inv PROMISE.
      exploit promise_consistent_promise_write; eauto; try by destruct msg1. i.
      inv MEM. inv SPLIT. timetac.
    - ii. subst. ss. inv STEP1.
      exploit Memory.promise_get2; eauto. i. des. inv PROMISE.
      exploit promise_consistent_promise_write; eauto. i.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      inv STEP2. ss. inv WRITE. inv PROMISE.
      exploit Memory.split_get0; try exact PROMISES0. i. des.
      rewrite GET2 in *. inv GET4.
      inv MEM1. inv SPLIT. timetac. }
  { i. subst. inv STEP1. inv PROMISE.
    exploit Memory.add_get0; try exact PROMISES. i. des.
    exploit promise_consistent_promise_write; try exact GET0; eauto; ss. i.
    inv x0; ss. inv H.
    inv STEP2. inv WRITE. inv PROMISE. ss.
    exploit Memory.add_get0; try exact MEM. i. des.
    exploit Memory.add_get0; try exact MEM1. i. des. congr. }
Qed.

Lemma reorder_promise_write_memory
      promises0 mem0
      promises1 mem1
      promises2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 msg2 kind2
      (PROMISE: Memory.promise promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 kind1)
      (WRITE: Memory.write promises1 mem1 loc2 from2 to2 msg2 promises2 mem2 kind2)
      (NONPF: Memory.op_kind_is_cancel kind1 = false)
      (CONS: forall f t m
               (GET: Memory.get loc2 t promises2 = Some (f, m))
               (RESERVE: m <> Message.reserve),
          Time.lt to2 t):
  exists kind2' promises1' mem1',
    (<<WRITE: Memory.write promises0 mem0 loc2 from2 to2 msg2 promises1' mem1' kind2'>>) /\
    (<<PROMISE: __guard__
                  ((promises2, mem2, loc1) = (promises1', mem1', loc2) \/
                   (exists from1' kind1',
                       Memory.promise promises1' mem1' loc1 from1' to1 msg1 promises2 mem2 kind1' /\
                       Memory.op_kind_is_cancel kind1' = false))>>).
Proof.
  exploit Memory.write_not_cancel; eauto. intro KIND2.
  inv WRITE. inv PROMISE; inv PROMISE0; ss.
  { (* add-add *)
    exploit MemoryReorder.add_add; try exact PROMISES; eauto. i. des.
    exploit MemoryReorder.add_add; try exact MEM; eauto. i. des.
    exploit MemoryReorder.add_remove; try exact ADD2; eauto. i. des.
    esplits.
    - econs; eauto. econs 1; eauto. i.
      exploit Memory.add_get1; try exact MEM; eauto.
    - right. esplits.
      + econs 1; eauto. i.
        revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto.
        i. des. inv GET.
        exploit Memory.add_get0; try exact ADD4. i. des.
        exploit CONS; eauto. intros x.
        inv MEM0. inv ADD. rewrite x in TO. timetac.
      + ss.
  }

  { (* add-split *)
    exploit MemoryReorder.add_split; try exact PROMISES; eauto. i.
    exploit MemoryReorder.add_split; try exact MEM; eauto. i.
    des; subst; ss.
    { clear x1 x2 x3 x4.
      exploit MemoryReorder.add_remove; try exact ADD3; eauto.
      { ii. inv H. inv ADD3. inv ADD. timetac. }
      i. des. esplits.
      - econs; eauto. econs 1; eauto. i.
        exploit Memory.split_get0; try exact MEM0. i. des.
        exploit Memory.add_get1; try exact MEM; eauto. i.
        exploit Memory.get_disjoint; [exact GET1|exact x0|]. i. des.
        + subst. inv ADD0. inv ADD. timetac.
        + inv MEM0. inv SPLIT.
          destruct (TimeFacts.le_lt_dec ts3 to').
          * apply (x1 ts3); econs; ss; try refl. etrans; eauto.
          * apply (x1 to'); econs; ss; try refl.
            { exploit Memory.get_ts; try exact x0. i. des.
              - subst. timetac.
              - etrans; eauto.
            }
            { econs. ss. }
            { exploit Memory.get_ts; try exact x0. i. des; ss.
              subst. inv TS12.
            }
      - right. esplits.
        + econs 1; eauto. i.
          exploit Memory.add_get1; try exact GET; eauto.
          erewrite Memory.split_o; eauto. repeat (condtac; ss).
          { i. des. inv x0.
            inv MEM0. inv SPLIT. rewrite TS12 in TS23. timetac. }
          { guardH o. i. des. inv x0.
            inv MEM0. inv SPLIT. timetac. }
          guardH o. guardH o0.
          erewrite Memory.add_o; eauto. condtac; ss; eauto.
        + ss.
    }
    { exploit MemoryReorder.add_remove; try exact ADD0; try exact REMOVE; eauto.
      { ii. inv H.
        exploit Memory.add_get0; try exact PROMISES. i. des.
        exploit Memory.split_get0; try exact PROMISES0. i. des.
        exploit Memory.get_disjoint; [exact GET0|exact GET2|]. i. des.
        { subst. inv MEM0. inv SPLIT. timetac. }
        inv MEM0. inv SPLIT. apply (x0 to2); econs; ss; try refl.
        - inv MEM. inv ADD. ss.
        - econs. ss.
      }
      i. des. esplits; eauto.
      right. esplits.
      - econs 1; eauto. i. revert GET.
        erewrite Memory.split_o; eauto. repeat (condtac; ss); eauto.
        + i. des. inv GET.
          exploit Memory.split_get0; try exact MEM0. i. des. revert GET0.
          erewrite Memory.add_o; eauto. condtac; ss; eauto.
          i. des. inv GET0. inv MEM. inv ADD. timetac.
        + guardH o. i. des. inv GET.
          exploit Memory.add_get0; try exact MEM. i. des.
          exploit Memory.split_get0; try exact MEM0. i. des. congr.
      - ss.
    }
  }

  { (* add-lower *)
    exploit MemoryReorder.add_lower; try exact PROMISES; eauto. i.
    exploit MemoryReorder.add_lower; try exact MEM; eauto. i.
    des; subst; ss.
    { clear x1 x2 x3 x4.
      exploit Memory.add_get0; try exact x9. intros x. des.
      exploit Memory.remove_exists; try exact GET0. i. des.
      esplits.
      - econs; try exact x0. econs 1; eauto. i.
        eapply ATTACH; eauto. ii. subst.
        inv MEM0. inv LOWER. inv MSG_LE. ss.
      - left. f_equal. f_equal.
        apply Memory.ext. i.
        erewrite (@Memory.remove_o promises2); eauto.
        erewrite (@Memory.remove_o mem3); eauto.
    }
    { exploit MemoryReorder.add_remove; try exact ADD0; eauto. i. des.
      esplits; eauto. right. esplits.
      - econs 1; eauto. i. revert GET.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        i. des. inv GET.
        exploit Memory.add_get0; try exact PROMISES. i. des.
        exploit Memory.lower_get1; try exact GET0; eauto. i. des.
        exploit Memory.remove_get1; try exact GET2; eauto. i. des; subst; ss.
        exploit CONS; try exact GET1; eauto.
        { ii. subst. inv MSG_LE. ss. }
        intros x. inv PROMISES0. inv LOWER. rewrite TS1 in x. timetac.
      - ss.
    }
  }

  { (* split-add *)
    exploit MemoryReorder.split_add; try exact PROMISES; eauto. i. des.
    exploit MemoryReorder.split_add; try exact MEM; eauto. i. des.
    exploit MemoryReorder.split_remove; try exact SPLIT2; eauto. i. des.
    esplits.
    - econs; eauto. econs 1; eauto. i.
      destruct (Memory.get loc2 to' mem1) as [[]|] eqn:GET'; cycle 1.
      { revert GET'. erewrite Memory.split_o; eauto.
        repeat condtac; ss. congr.
      }
      exploit Memory.split_get0; try exact MEM. i. des.
      dup GET'. revert GET'. erewrite Memory.split_o; eauto.
      repeat (condtac; ss).
      + i. des. inv GET'. congr.
      + guardH o. i. des. inv GET'.
        rewrite GET in *. inv GET1. eauto.
      + i. rewrite GET in *. inv GET'. eauto.
    - right. esplits; eauto.
  }

  { (* split-split *)
    assert (LOCTS: (loc1, ts3) <> (loc2, ts0)).
    { ii. inv H.
      exploit Memory.split_get0; try exact PROMISES. intros x. des.
      exploit Memory.split_get0; try exact PROMISES0. intros x. des.
      rewrite GET2 in *. inv GET4.
      destruct (Memory.get loc2 from2 promises2) as [[]|] eqn:GET'.
      { exploit CONS; try exact GET'.
        - ii. subst. revert GET'.
          erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
          erewrite Memory.split_o; eauto. repeat (condtac; ss); eauto.
          + guardH o0. i. des. inv GET'. ss.
          + guardH o0. guardH o1. i. rewrite GET' in *. inv GET1. ss.
        - intros x. inv PROMISES0. inv SPLIT. rewrite x in TS12. timetac.
      }
      { revert GET'. erewrite Memory.remove_o; eauto. condtac; ss.
        - des. subst. inv MEM0. inv SPLIT. timetac.
        - erewrite Memory.split_o; eauto. repeat (condtac; ss); eauto. congr.
      }
    }
    exploit MemoryReorder.split_split; try exact PROMISES; eauto. i.
    exploit MemoryReorder.split_split; try exact MEM; eauto. i.
    des; subst; ss.
    - exploit MemoryReorder.split_remove; try exact SPLIT3; try exact REMOVE; eauto.
      { ii. inv H. inv MEM0. inv SPLIT. timetac. }
      { ii. inv H. inv MEM. inv SPLIT. inv MEM0. inv SPLIT.
        rewrite TS23 in TS2. timetac. }
      i. des. esplits; eauto.
      right. esplits; eauto.
    - exploit MemoryReorder.split_remove; try exact SPLIT3; try exact REMOVE; eauto.
      { ii. inv H.
        exploit Memory.split_get0; try exact MEM. i. des.
        exploit Memory.split_get0; try exact MEM0. i. des. congr. }
      { ii. inv H.
        exploit Memory.split_get0; try exact MEM. i. des.
        exploit Memory.split_get0; try exact MEM0. i. des. congr. }
      i. des. esplits; eauto.
      right. esplits; eauto.
  }

  { (* split-lower *)
    destruct (classic ((loc1, ts3) = (loc2, to2))).
    { inv H. exfalso.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      destruct (Memory.get loc2 to1 promises2) as [[]|] eqn:GET'.
      { dup GET'. revert GET'.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.lower_o; eauto. condtac; ss.
        i. rewrite GET' in *. inv GET1.
        exploit CONS; try exact GET'0; eauto. intros x.
        inv MEM. inv SPLIT. rewrite x in TS23. timetac.
      }
      { revert GET'.
        erewrite Memory.remove_o; eauto. condtac; ss.
        - des. subst. inv MEM. inv SPLIT. timetac.
        - erewrite Memory.lower_o; eauto. condtac; ss. congr.
      }
    }
    exploit MemoryReorder.split_lower_diff; try exact PROMISES; eauto. i.
    exploit MemoryReorder.split_lower_diff; try exact MEM; eauto. i.
    des; subst; ss.
    - clear x1 x2 x3 x4. esplits; eauto. left. ss.
    - exploit MemoryReorder.split_remove; try exact SPLIT0; eauto. i. des.
      esplits; eauto.
      right. esplits; eauto.
  }

  { (* lower-add *)
    exploit MemoryReorder.lower_add; try exact PROMISES; eauto. i. des.
    exploit MemoryReorder.lower_add; try exact MEM; eauto. i. des.
    exploit MemoryReorder.lower_remove; try exact LOWER2; eauto. i. des.
    esplits.
    - econs; eauto. econs 1; eauto. i.
      exploit Memory.lower_get1; try exact GET; eauto. i. des.
      eapply ATTACH; try exact GET2; eauto.
    - right. esplits; eauto.
  }

  { (* lower-split *)
    exploit MemoryReorder.lower_split; try exact PROMISES; eauto. i.
    exploit MemoryReorder.lower_split; try exact MEM; eauto. i.
    unguardH x0. unguardH x1. des; try inv FROM0; try inv FROM1; ss.
    { exploit MemoryReorder.lower_remove; try exact LOWER0; eauto.
      { ii. inv H. inv SPLIT0. inv SPLIT. timetac. }
      i. des. esplits.
      - econs; eauto. econs 2; eauto. ii. subst.
        inv MEM. inv LOWER. inv MSG_LE. ss.
      - right. esplits; eauto.
    }
    { inv FROM3. inv FROM2.
      exploit MemoryReorder.lower_remove; try exact LOWER0; try exact REMOVE; eauto.
      { ii. inv H.
        exploit Memory.lower_get0; try exact MEM. i. des.
        exploit Memory.split_get0; try exact MEM0. i. des. congr.
      }
      i. des. esplits; eauto. right. eauto.
    }
  }

  { (* lower-lower *)
    exploit MemoryReorder.lower_lower; try exact PROMISES; eauto. i.
    exploit MemoryReorder.lower_lower; try exact MEM; eauto. i.
    des; subst; ss.
    { esplits; eauto. left. ss. }
    { exploit MemoryReorder.lower_remove; try exact LOWER3; eauto. i. des.
      esplits; eauto. right. eauto.
    }
  }
Qed.

Lemma write_promise_consistent
      ts
      promises1 mem1 loc from to msg promises2 mem2 kind
      (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind)
      (CONS: forall f t m
               (GET: Memory.get loc t promises2 = Some (f, m))
               (RESERVE: m <> Message.reserve),
          Time.lt to t)
      (TS: Time.lt ts to):
  forall f t m
    (GET: Memory.get loc t promises1 = Some (f, m))
    (RESERVE: m <> Message.reserve),
    Time.lt ts t.
Proof.
  exploit Memory.write_not_cancel; eauto. i.
  inv WRITE. inv PROMISE; ss; i.
  - exploit Memory.add_get1; try exact GET; eauto. i.
    exploit Memory.remove_get1; try exact x1; eauto. i. des.
    { subst. exploit Memory.add_get0; try exact PROMISES. i. des. congr. }
    exploit CONS; try exact GET2; eauto.
  - exploit Memory.split_get1; try exact GET; eauto. i. des.
    exploit Memory.remove_get1; try exact GET2; eauto. i. des.
    { subst. exploit Memory.split_get0; try exact PROMISES. i. des. congr. }
    exploit CONS; try exact GET0; eauto.
  - exploit Memory.lower_get1; try exact GET; eauto. i. des.
    exploit Memory.remove_get1; try exact GET2; eauto. i. des.
    { subst. exploit Memory.lower_get0; try exact PROMISES. i. des. congr. }
    exploit CONS; try exact GET0; eauto.
    { ii. subst. inv MSG_LE. ss. }
Qed.

Lemma write_na_promise_consistent
      ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
      (WRITE: Memory.write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
      (CONS: forall f t m
               (GET: Memory.get loc t promises2 = Some (f, m))
               (RESERVE: m <> Message.reserve),
          Time.lt to t):
  forall f t m
    (GET: Memory.get loc t promises1 = Some (f, m))
    (RESERVE: m <> Message.reserve),
    Time.lt ts t.
Proof.
  induction WRITE; eauto using write_promise_consistent.
Qed.

Lemma reorder_promise_write_na_memory
      promises0 mem0
      promises1 mem1
      promises2 mem2
      loc1 from1 to1 msg1 kind1
      ts loc2 from2 to2 val2 msgs2 kinds2 kind2
      (PROMISE: Memory.promise promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 kind1)
      (WRITE: Memory.write_na ts promises1 mem1 loc2 from2 to2 val2 promises2 mem2 msgs2 kinds2 kind2)
      (NONPF: Memory.op_kind_is_cancel kind1 = false)
      (CONS: forall f t m
               (GET: Memory.get loc2 t promises2 = Some (f, m))
               (RESERVE: m <> Message.reserve),
          Time.lt to2 t):
  exists kinds2' kind2' promises1' mem1',
    <<WRITE: Memory.write_na ts promises0 mem0 loc2 from2 to2 val2 promises1' mem1' msgs2 kinds2' kind2'>> /\
    (<<PROMISE: __guard__
                  ((promises2, mem2, loc1) = (promises1', mem1', loc2) \/
                   (exists from1' kind1',
                       Memory.promise promises1' mem1' loc1 from1' to1 msg1 promises2 mem2 kind1'))>>).
Proof.
  revert promises0 mem0 loc1 from1 to1 msg1 kind1 PROMISE NONPF.
  induction WRITE; i.
  { exploit reorder_promise_write_memory; eauto. i. des.
    esplits; eauto.
    unguardH PROMISE0. des; [left|right]; eauto.
    }
  exploit reorder_promise_write_memory; try exact PROMISE; eauto.
  { eapply write_na_promise_consistent; eauto. }
  i. unguardH x0. des.
  { inv PROMISE0. esplits; eauto. left. ss. }
  exploit IHWRITE; try exact PROMISE0; eauto.
  intros x. unguardH x. des.
  - inv PROMISE1. esplits; eauto. left. ss.
  - esplits; eauto. right. esplits; eauto.
Qed.

Lemma reorder_promise_write_na
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 ord2 msgs2 kinds2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_na_step lc1 sc0 mem1 loc2 from2 to2 val2 ord2 lc2 sc2 mem2 msgs2 kinds2 kind2)
      (NONPF: Memory.op_kind_is_cancel kind1 = false)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (CONS: Local.promise_consistent lc2):
  (exists kinds2' kind2' lc1' mem1',
     <<STEP1: Local.write_na_step lc0 sc0 mem0 loc2 from2 to2 val2 ord2 lc1' sc2 mem1' msgs2 kinds2' kind2'>> /\
     <<STEP2: __guard__
                ((lc2, mem2, loc1) = (lc1', mem1', loc2) \/
                 (exists from1' kind1',
                     <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>>).
Proof.
  exploit Local.promise_step_future; eauto. i. des.
  exploit Local.write_na_step_future; eauto. i. des.
  inv STEP1. inv STEP2. ss.
  exploit reorder_promise_write_na_memory; eauto.
  { i. exploit CONS; eauto. s. i.
    eapply TimeFacts.le_lt_lt; eauto.
    unfold TimeMap.join, TimeMap.singleton, Loc.LocFun.add, Loc.LocFun.find.
    condtac; ss. apply Time.join_r.
  }
  i. des. esplits; eauto.
  unguardH PROMISE0. des.
  - inv PROMISE0. left. ss.
  - right. esplits. econs; eauto.
    eapply Memory.future_closed_message; eauto.
Qed.


#[export] Hint Constructors Thread.program_step: core.
#[export] Hint Constructors Thread.step: core.

Lemma reorder_nonpf_program
      lang
      e1 e2 th0 th1 th2
      (STEP1: @Thread.step lang false e1 th0 th1)
      (STEP2: Thread.program_step e2 th1 th2)
      (CONS2: Local.promise_consistent (Thread.local th2))
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0)):
  exists th1',
     <<STEP1: Thread.program_step e2 th0 th1'>> /\
     <<STEP2: __guard__ (th2 = th1' \/ exists pf2' e2', Thread.promise_step pf2' e2' th1' th2)>>.
Proof.
  exploit Thread.step_future; eauto. i. des.
  inv STEP1. inv STEP. ss. inv STEP2. inv LOCAL1; ss.
  - (* silent *)
    esplits; eauto.
    right. esplits. econs; eauto.
  - (* read *)
    exploit reorder_promise_read; try exact LOCAL0; eauto; try by viewtac.
    { ii. inv H.
      inv LOCAL0. exploit Memory.promise_get2; eauto.
      { destruct kind, msg; ss. }
      i. des.
      dup LOCAL2. inv LOCAL0. ss.
      rewrite GET in *. inv GET_MEM.
      hexploit promise_consistent_promise_read; eauto. i. timetac.
    }
    i. des. esplits.
    + econs; eauto.
    + right. esplits. econs; eauto.
  - (* write *)
    exploit reorder_promise_write; try exact LOCAL0; eauto.
    { destruct kind, msg; ss; eauto. repeat condtac; ss; eauto. }
    { destruct kind, msg; ss. }
    i. des. esplits.
    + econs; eauto.
    + unguardH STEP2. des.
      * inv STEP2. left. auto.
      * right. esplits. econs; eauto.
  - (* update *)
    exploit reorder_promise_read; try exact LOCAL1; eauto; try by viewtac.
    { ii. inv H.
      inv LOCAL0. exploit Memory.promise_get2; eauto.
      { destruct kind, msg; ss. }
      i. des.
      dup LOCAL2. inv LOCAL0. ss.
      rewrite GET in *. inv GET_MEM.
      exploit promise_consistent_promise_read; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. eapply Time.lt_strorder. eauto.
    }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit reorder_promise_write; try exact LOCAL2; eauto; try by viewtac.
    { destruct kind, msg; ss; eauto. repeat condtac; ss; eauto. }
    { destruct kind, msg; ss. }
    i. des. esplits.
    + econs; eauto.
    + unguardH STEP3. des.
      * inv STEP3. left. auto.
      * right. esplits. econs; eauto.
  - (* fence *)
    inv LOCAL0. inv LOCAL2.
    esplits; eauto.
    + econs; eauto. econs 5; eauto. econs; eauto; cycle 1.
      { i. subst. ss. erewrite PROMISES in *; eauto.
        eapply Memory.ext. i. erewrite Memory.bot_get.
        destruct (Memory.get loc0 ts (Local.promises lc1)) as [[from0 msg0]|] eqn:GET; auto.
        eapply Memory.promise_get1_promise in GET; try apply PROMISE.
        { des. erewrite Memory.bot_get in *. ss. }
        { destruct kind; ss. }
      }
      ss. intros ORDW l. eapply promise_step_nonsynch_loc_inv; eauto.
      * destruct msg, kind; ss; eauto. repeat condtac; ss; eauto.
      * apply RELEASE. ss.
    + right. esplits. econs; eauto.
  - (* syscall *)
    inv LOCAL0. inv LOCAL2.
    esplits; eauto.
    + econs; eauto. econs 6; eauto. econs; eauto; cycle 1.
      { i. subst. ss. erewrite PROMISES in *; eauto.
        eapply Memory.ext. i. erewrite Memory.bot_get.
        destruct (Memory.get loc0 ts (Local.promises lc1)) as [[from0 msg0]|] eqn:GET; auto.
        eapply Memory.promise_get1_promise in GET; try apply PROMISE.
        { des. erewrite Memory.bot_get in *. ss. }
        { destruct kind; ss. }
      }
      intros ORDW l. eapply promise_step_nonsynch_loc_inv; eauto.
      * destruct msg, kind; ss; eauto. repeat condtac; ss; eauto.
      * apply RELEASE. ss.
    + right. esplits. econs; eauto.
  - (* failure *)
    inv LOCAL2.
    hexploit promise_step_promise_consistent; eauto. i.
    esplits; eauto.
    right. esplits. econs; eauto.
  - (* na write *)
    exploit reorder_promise_write_na; try exact LOCAL0; eauto.
    { destruct kind, msg; ss. }
    i. des. esplits.
    + econs; eauto.
    + unguardH STEP2. des.
      * inv STEP2. left. auto.
      * right. esplits. econs; eauto.
  - (* racy read *)
    inv LOCAL0. inv LOCAL2. inv RACE. ss.
    exploit MemoryFacts.promise_get_inv_diff; try exact PROMISE; eauto.
    { ii. inv H.
      exploit Memory.promise_get2; try exact PROMISE; try by (destruct kind; ss). i. des. congr. }
    i. des.
    destruct (Memory.get loc0 to0 lc1.(Local.promises)) as [[]|] eqn:GETP1.
    { exploit Memory.promise_get1_promise; eauto; try by (destruct kind; ss). i. des. congr. }
    esplits; eauto. right. esplits. econs; eauto.
  - (* racy write *)
    inv LOCAL0. inv LOCAL2. inv RACE. ss.
    hexploit promise_step_promise_consistent; eauto. i.
    exploit MemoryFacts.promise_get_inv_diff; try exact PROMISE; eauto.
    { ii. inv H0.
      exploit Memory.promise_get2; try exact PROMISE; try by (destruct kind; ss). i. des. congr. }
    i. des.
    destruct (Memory.get loc0 to0 lc1.(Local.promises)) as [[]|] eqn:GETP1.
    { exploit Memory.promise_get1_promise; eauto; try by (destruct kind; ss). i. des. congr. }
    esplits; eauto. right. esplits. econs; eauto.
  - (* racy update *)
    hexploit promise_step_promise_consistent; eauto. i.
    inv LOCAL0. inv LOCAL2; ss.
    { esplits; eauto. right. esplits. econs; eauto. }
    { esplits; eauto. right. esplits. econs; eauto. }
    inv RACE. ss.
    exploit MemoryFacts.promise_get_inv_diff; try exact PROMISE; eauto.
    { ii. inv H0.
      exploit Memory.promise_get2; try exact PROMISE; try by (destruct kind; ss). i. des. congr. }
    i. des.
    destruct (Memory.get loc0 to0 lc1.(Local.promises)) as [[]|] eqn:GETP1.
    { exploit Memory.promise_get1_promise; eauto; try by (destruct kind; ss). i. des. congr. }
    esplits; eauto.
    right. esplits. econs; eauto.
Qed.

Lemma reorder_nonpf_pf
      lang
      e1 e2 th0 th1 th2
      (STEP1: @Thread.step lang false e1 th0 th1)
      (STEP2: Thread.step true e2 th1 th2)
      (CONS2: Local.promise_consistent (Thread.local th2))
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0)):
  (th0 = th2) \/
  (exists pf2' e2',
      <<STEP: Thread.step pf2' e2' th0 th2>> /\
      <<EVENT: __guard__ (e2' = e2 \/ (ThreadEvent.is_promising e2' /\ ThreadEvent.is_promising e2))>>) \/
  (exists e2' pf1' e1' th1',
      <<STEP1: Thread.step true e2' th0 th1'>> /\
      <<STEP2: Thread.promise_step pf1' e1' th1' th2>> /\
      <<EVENT: __guard__ (e2' = e2 \/ (ThreadEvent.is_promising e2' /\ ThreadEvent.is_promising e2))>>).
Proof.
  inv STEP2; ss.
  - inv STEP. ss.
    inv STEP1. inv STEP. ss.
    destruct kind; ss.
    + destruct msg1, msg; ss; cycle 1.
      { inv LOCAL0. inv PROMISE. inv MEM. inv LOWER. inv MSG_LE. }
      { inv LOCAL0. inv PROMISE. inv MEM. inv LOWER. inv MSG_LE. }
      destruct released0; ss.
      exploit reorder_promise_promise_lower_None; eauto.
      { destruct kind0; ss. }
      i. des; subst.
      * right. left. esplits.
        { econs 1. econs; eauto. }
        { right. ss. }
      * right. right. esplits.
        { econs 1. econs; eauto. }
        { econs; eauto. }
        { right. ss. }
    + exploit reorder_promise_promise_cancel; eauto.
      i. des; subst; eauto.
      right. right. esplits.
      { econs 1. econs; eauto. }
      { econs; eauto. }
      { right. ss. }
  - exploit reorder_nonpf_program; eauto. i. des.
    unguardH STEP2. des.
    + subst. right. left. esplits; eauto. left. ss.
    + right. right. esplits; eauto. left. ss.
Qed.
