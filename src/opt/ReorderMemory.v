Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma fulfill_promise
      promises1 loc1 to1 msg1
      promises2 loc2 from2 to2 msg2
      promises3
      mem1 mem3
      (CLOSED: Memory.closed_promises promises1 mem1)
      (FULFILL: Memory.fulfill promises1 mem1 loc1 to1 msg1 promises2)
      (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 msg2 promises3 mem3):
  exists promises2',
    Memory.promise promises1 mem1 loc2 from2 to2 msg2 promises2' mem3 /\
    Memory.fulfill promises2' mem3 loc1 to1 msg1 promises3.
Proof.
  inv FULFILL. inv PROMISE.
  - eexists. splits.
    + econs 1; eauto.
    + admit.
  - eexists. splits.
    + econs 2; eauto.
      admit.
    + admit.
Admitted.

Lemma get_fulfill
      promises0 mem0 loc to msg promises1
      l t m
      (LOC: loc <> l)
      (CLOSED: Memory.closed_promises promises0 mem0)
      (GET: Memory.get l t mem0 = Some m)
      (FULFILL: Memory.fulfill promises0 mem0 loc to msg promises1):
  Promises.mem l t promises0 = Promises.mem l t promises1.
Proof.
  inv FULFILL. admit.
Admitted.

Lemma cell_fulfill
      promises0 mem0 loc to msg promises1
      l
      (LOC: loc <> l)
      (FULFILL: Memory.fulfill promises0 mem0 loc to msg promises1):
  promises0 l = promises1 l.
Proof.
  inv FULFILL. admit.
Admitted.

Lemma fulfill_fulfill
      promises1 loc1 to1 msg1
      promises2 loc2 to2 msg2
      promises3
      mem1
      (FULFILL1: Memory.fulfill promises1 mem1 loc1 to1 msg1 promises2)
      (FULFILL2: Memory.fulfill promises2 mem1 loc2 to2 msg2 promises3):
  exists promises2',
    Memory.fulfill promises1 mem1 loc2 to2 msg2 promises2' /\
    Memory.fulfill promises2' mem1 loc1 to1 msg1 promises3.
Proof.
  inv FULFILL1. inv FULFILL2.
  eexists. splits.
  - econs; eauto.
    admit.
  - admit.
Admitted.