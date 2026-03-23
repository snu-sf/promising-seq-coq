From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import RelationClasses.
From Stdlib Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import lang.Time.
Require Import lang.View.
Require Import lang.Cell.
Require Import lang.Memory.
Require Import lang.TView.
Require Import lang.Local.
Require Import lang.Thread.
Require Import lang.Configuration.
Require Import lang.Behavior.

Require Import prop.Single.
Require Import prop.JoinedView.

Require Import ldrfpf.LocalDRFPFView.

Require Import ldrfra.OrdStep.
Require Import ldrfra.Stable.
Require Import ldrfra.WStep.
Require Import ldrfra.PFtoRA.
Require Import ldrfra.RARace.

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
