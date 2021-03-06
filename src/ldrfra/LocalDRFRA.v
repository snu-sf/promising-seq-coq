Require Import Lia.
Require Import Bool.
Require Import RelationClasses.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import Single.
Require Import JoinedView.

Require Import LocalDRFPFView.

Require Import OrdStep.
Require Import Stable.
Require Import WStep.
Require Import PFtoRA.
Require Import RARace.

Set Implicit Arguments.


(* LDRF-RA theorem *)
Theorem local_drf_ra L
        s
        (RACEFREE: RARace.racefree_syn L s):
  behaviors SConfiguration.machine_step (Configuration.init s) <2=
  behaviors (@OrdConfiguration.machine_step L Ordering.acqrel Ordering.acqrel) (Configuration.init s).
Proof.
  hexploit RARace.racefree_implies; eauto. i.
  specialize (PFtoRA.init_sim_conf L s). intro SIM.
  specialize (PFtoRA.init_wf_pf L s). intro WF_PF.
  specialize (PFtoRA.init_wf_j s). intro WF_J.
  specialize (PFtoRA.init_wf_ra L s). intro WF_APF.
  specialize (PFtoRA.init_wf_ra L s). intro WF_RA.
  ii. exploit (@local_drf_pf_view L); eauto.
  { eapply PFtoRA.sim_conf_racefree; eauto. }
  eapply PFtoRA.sim_conf_behavior; eauto.
Qed.
