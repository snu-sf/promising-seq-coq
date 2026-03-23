From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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
Require Import lang.Progress.

Require Import transformation.SimMemory.
Require Import transformation.SimPromises.
Require Import transformation.SimLocal.
Require Import transformation.SimThread.
Require Import transformation.iCompatibility.

Require Import itree.ITreeLang.

Set Implicit Arguments.


Lemma intro_load_sim_itree
      loc ord:
  sim_itree eq
            (Ret tt)
            (ITree.trigger (MemE.read loc ord);; Ret tt).
Proof.
  unfold trigger. rewrite bind_vis.
  pcofix CIH. ii. subst. pfold. ii. splits; i.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. right.
  inv STEP_TGT; inv STEP; ss; try (dependent destruction STATE); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    esplits; [|refl|econs 1|..]; eauto.
    + destruct e_tgt; ss.
    + destruct e_tgt; ss.
    + sfby inv LOCAL0.
    + sfby inv LOCAL0.
    + left. rewrite bind_ret_l. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      inv LOCAL. inv LOCAL0; ss. inv LOCAL. econs; ss.
      etrans; eauto. apply TViewFacts.read_tview_incr.
Qed.
