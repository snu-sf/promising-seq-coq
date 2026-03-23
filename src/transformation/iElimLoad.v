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

Require Import transformation.ElimLoadCommon.

Set Implicit Arguments.

(* NOTE: Elimination of a unused relaxed load is unsound under the
 * liveness-aware semantics.  Consider the following example:

    while (!y_plain) {
        r = x_rlx;
        fence(acquire);
    }

    ||

    y =rlx 1;
    x =rel 1;

 * Under the liveness-aware semantics, the loop *should* break, as
 * once `x_rlx` will read `x =rel 1` and the acquire fence guarantees
 * that `y_plain` will read 1.  However, the elimination of
 * `x_rlx` will allow the loop to run forever.
 *)

Lemma elim_load_sim_itree
      loc ord
      (ORD: Ordering.le ord Ordering.plain):
  sim_itree (fun _ _ => True)
            (ITree.trigger (MemE.read loc ord);; Ret tt)
            (Ret tt).
Proof.
  unfold trigger. rewrite bind_vis.
  pcofix CIH. ii. subst. pfold. ii. splits; i.
  { right.
    exploit elim_read; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    esplits.
    - econs 2; eauto. econs.
      + econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
    - auto.
    - auto.
    - rewrite bind_ret_l. auto.
    - auto.
    - rewrite bind_ret_l. econs; eauto.
  }
  { i. right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. right.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  (* promise *)
  exploit sim_local_promise; eauto. i. des.
  esplits; try apply SC; eauto; ss.
  econs 2. econs 1; eauto. econs; eauto. eauto.
Qed.
