Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import SimMemory.
Require Import Simulation.

Set Implicit Arguments.


Lemma sim_adequacy
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (WF_SRC: Configuration.wf (Configuration.mk ths_src sc_src mem_src))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (SC: TimeMap.le sc_src sc_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (SIM: sim ths_src sc_src mem_src ths_tgt sc_tgt mem_tgt):
  behaviors Configuration.step (Configuration.mk ths_tgt sc_tgt mem_tgt) <2=
  behaviors Configuration.step (Configuration.mk ths_src sc_src mem_src).
Proof.
  s. i.
  revert WF_SRC WF_TGT SC MEMORY SIM.
  revert ths_src sc_src mem_src.
  dependent induction PR; i.
  - punfold SIM. exploit SIM; eauto; try refl. i. des.
    exploit TERMINAL0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + eapply rtc_tau_step_behavior; eauto.
      econs 1. eauto.
  - destruct c2.
    punfold SIM. exploit SIM; eauto; try refl. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + inv SIM0; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try apply STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv STEP_SRC. econs 2; eauto.
      exploit Configuration.step_future; try apply STEP1; eauto. i. des.
      eapply IHPR; eauto.
  - destruct c2.
    punfold SIM. exploit SIM; eauto; try refl. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM0; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try apply STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv STEP_SRC. econs 3; eauto.
  - destruct c2.
    punfold SIM. exploit SIM; eauto; try refl. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM0; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try apply STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv STEP_SRC.
      * eapply IHPR; eauto.
      * econs 4; eauto.
        exploit Configuration.step_future; try apply STEP1; eauto. s. i. des.
        eapply IHPR; eauto.
  - econs 5.
Qed.
