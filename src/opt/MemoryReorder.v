Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.

Set Implicit Arguments.


Module MemoryReorder.
  Lemma add_add
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2).
    { i. exploit Memory.add_get1; try exact ADD1; eauto. i. des.
      inv ADD2. inv ADD. eauto.
    }
    { inv ADD2. inv ADD. auto. }
    { inv ADD2. inv ADD. eauto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1).
    { i. exploit Memory.add_get_inv; try exact x0; eauto. i. des.
      { subst. exploit Memory.add_get2; try exact ADD1; eauto. i.
        inv ADD2. inv ADD. symmetry. eauto.
      }
      inv ADD1. inv ADD. eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite MemoryFacts.add_o; eauto.
    erewrite MemoryFacts.add_o; eauto.
    erewrite (@MemoryFacts.add_o mem2); eauto.
    erewrite (@MemoryFacts.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get2; try exact ADD1; eauto. i.
    exploit Memory.add_get0; try exact ADD2; eauto. i. congr.
  Qed.

  Lemma promise_add_promise_add
        loc1 from1 to1 val1 released1
        loc2 from2 to2 val2 released2
        promises0 mem0
        promises1 mem1
        promises2 mem2
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 val1 released1 promises1 mem1 Memory.promise_kind_add)
        (PROMISE2: Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2 mem2 Memory.promise_kind_add):
    exists promises1' mem1',
      <<PROMISE1: Memory.promise promises0 mem0 loc2 from2 to2 val2 released2 promises1' mem1' Memory.promise_kind_add>> /\
      <<PROMISE2: Memory.promise promises1' mem1' loc1 from1 to1 val1 released1 promises2 mem2 Memory.promise_kind_add>>.
  Proof.
    inv PROMISE1. inv PROMISE2.
    exploit add_add; try exact PROMISES; eauto. i. des.
    exploit add_add; try exact MEM; eauto. i. des.
    esplits.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma add_remove
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        (DIFF: (loc1, to1) <> (loc2, to2))
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>.
  Proof.
    exploit Memory.remove_get0; try exact REMOVE2; eauto. i.
    exploit Memory.add_get_inv; try exact ADD1; eauto. i. des.
    { inv x4. contradict DIFF. auto. }
    exploit Memory.remove_exists; try exact x2; eauto. i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1); eauto.
    { i. exploit Memory.remove_get_inv; try exact x3; eauto. i. des.
      inv ADD1. inv ADD. eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite MemoryFacts.add_o; eauto.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite (@MemoryFacts.remove_o mem2); eauto.
    erewrite (@MemoryFacts.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get0; try exact x0; eauto. congr.
  Qed.

  Lemma promise_add_remove
        loc1 from1 to1 val1 released1
        loc2 from2 to2 val2 released2
        promises0 mem0
        promises1 mem1
        promises2
        (DIFF: (loc1, to1) <> (loc2, to2))
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 val1 released1 promises1 mem1 Memory.promise_kind_add)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 val2 released2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 val2 released2 promises1'>> /\
      <<PROMISE2: Memory.promise promises1' mem0 loc1 from1 to1 val1 released1 promises2 mem1 Memory.promise_kind_add>>.
  Proof.
    inv PROMISE1.
    exploit add_remove; try exact PROMISES; eauto. i. des.
    esplits; eauto. econs; eauto.
  Qed.

  Lemma remove_add
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2)
        (ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit Memory.add_get1; try eexact ADD1; eauto. i.
    exploit Memory.remove_exists; try eexact x1; eauto. i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.add_o; eauto.
    erewrite (@MemoryFacts.add_o mem2); eauto.
    erewrite (@MemoryFacts.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    exploit Memory.add_get0; try eexact ADD1; eauto. congr.
  Qed.

  Lemma remove_update
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2' from2 to2 val2 released2' released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (UPDATE2: Memory.update mem1 loc2 from2' from2 to2 val2 released2' released2 mem2)
        (UPDATE1: Memory.update mem0 loc2 from2' from2 to2 val2 released2' released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit Memory.update_get1; try eexact UPDATE1; eauto. i. des.
    { inv x4. exploit Memory.remove_get2; try eexact REMOVE1; eauto. i.
      exploit Memory.update_get0; try eexact UPDATE2; eauto. i. congr.
    }
    exploit Memory.remove_exists; try eexact x2; eauto. i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.update_o; eauto.
    erewrite (@MemoryFacts.update_o mem2); eauto.
    erewrite (@MemoryFacts.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    contradict x1. auto.
  Qed.

  Lemma remove_promise
        promises1 loc1 from1 to1 val1 released1
        promises2 loc2 from2 to2 val2 released2
        promises3
        mem1 mem3
        kind
        (LE: Memory.le promises1 mem1)
        (REMOVE: Memory.remove promises1 loc1 from1 to1 val1 released1 promises2)
        (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 val2 released2 promises3 mem3 kind):
    exists promises2',
      Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2' mem3 kind /\
      Memory.remove promises2' loc1 from1 to1 val1 released1 promises3.
  Proof.
    inv PROMISE.
    - exploit Memory.add_exists_le; eauto. i. des.
      exploit remove_add; eauto. i.
      esplits; eauto. econs; eauto.
    - exploit Memory.update_get0; try eexact PROMISES; eauto. i.
      exploit Memory.remove_get_inv; try eexact REMOVE; eauto. i. des.
      exploit Memory.update_exists; eauto; try by inv PROMISES; inv UPDATE; eauto. i. des.
      exploit remove_update; eauto. i.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma remove_remove
        promises0 loc1 from1 to1 val1 released1
        promises1 loc2 from2 to2 val2 released2
        promises2
        (REMOVE1: Memory.remove promises0 loc1 from1 to1 val1 released1 promises1)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 val2 released2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 val2 released2 promises1'>> /\
      <<REMOVE2: Memory.remove promises1' loc1 from1 to1 val1 released1 promises2>>.
  Proof.
    exploit Memory.remove_get0; try apply REMOVE2; eauto. i.
    exploit Memory.remove_get_inv; try apply REMOVE1; eauto. i. des.
    exploit Memory.remove_exists; eauto. i. des.
    exploit Memory.remove_get0; try apply REMOVE1; eauto. i.
    exploit Memory.remove_get1; try apply x3; eauto. i. des; [by contradict x1|].
    exploit Memory.remove_exists; eauto. i. des.
    cut (mem0 = promises2).
    { esplits; subst; eauto. }
    apply Memory.ext. i.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite (@MemoryFacts.remove_o promises2); eauto.
    erewrite (@MemoryFacts.remove_o promises1); eauto.
    repeat (condtac; ss).
  Qed.
End MemoryReorder.
