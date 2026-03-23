From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
Require Import lang.Configuration.
Require Import lang.Behavior.

Require Import itree.ITreeLang.
Require Import sequential.NoMix.
Require Import sequential.Sequential.
Require Import itree.SequentialITree.
Require Import itree.SequentialCompatibility.
Require Import sequential.SequentialITreeAdequacy.

Require Import optimizer.WRforwarding.
Require Import optimizer.WRforwardingProof2.

Require Import optimizer.RRforwarding.
Require Import optimizer.RRforwardingProof2.

Require Import optimizer.DeadStoreElim.
Require Import optimizer.DeadStoreElimProof3.

Require Import optimizer.LoadIntro.

Set Implicit Arguments.


Section ADEQUACY.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.
  Hypothesis LOCDISJOINT: forall loc (NA: loc_na loc) (AT: loc_at loc), False.

  Theorem WRforwarding_sound A
          (code: ITreeLang.block)
          (prog_src prog_tgt: (lang Const.t).(Language.syntax))
          (PROG_SRC: prog_src = eval_lang code)
          (PROG_TGT: prog_tgt = eval_lang (WRfwd_opt_alg code))
          (ctx_seq: itree MemE.t Const.t -> itree MemE.t A)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context loc_na loc_at Const.t A ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_tgt))
          (NOMIX_CTX:
             forall tid lang syn
                    (FIND: IdentMap.find tid ctx_ths = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_context; eauto.
    eapply WRfwd_sim; eauto.
  Qed.

  Theorem RRforwarding_sound A
          (code: ITreeLang.block)
          (prog_src prog_tgt: (lang Const.t).(Language.syntax))
          (PROG_SRC: prog_src = eval_lang code)
          (PROG_TGT: prog_tgt = eval_lang (RRfwd_opt_alg code))
          (ctx_seq: itree MemE.t Const.t -> itree MemE.t A)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context loc_na loc_at Const.t A ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_tgt))
          (NOMIX_CTX:
             forall tid lang syn
                    (FIND: IdentMap.find tid ctx_ths = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_context; eauto.
    eapply RRfwd_sim; eauto.
  Qed.

  Theorem LICM_LoadIntro_sound A
          (code: ITreeLang.block)
          (prog_src prog_tgt: (lang Const.t).(Language.syntax))
          (PROG_SRC: prog_src = eval_lang code)
          (PROG_TGT: prog_tgt = eval_lang (LICM_LoadIntro code))
          (ctx_seq: itree MemE.t Const.t -> itree MemE.t A)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context loc_na loc_at Const.t A ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_tgt))
          (NOMIX_CTX:
             forall tid lang syn
                    (FIND: IdentMap.find tid ctx_ths = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_context; eauto.
    eapply LICM_LoadIntro_sim; eauto.
  Qed.

  Theorem DeadStoreElim_sound A
          (code: ITreeLang.block)
          (prog_src prog_tgt: (lang Const.t).(Language.syntax))
          (PROG_SRC: prog_src = eval_lang code)
          (PROG_TGT: prog_tgt = eval_lang (DSE_opt_alg code))
          (ctx_seq: itree MemE.t Const.t -> itree MemE.t A)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context loc_na loc_at Const.t A ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_tgt))
          (NOMIX_CTX:
             forall tid lang syn
                    (FIND: IdentMap.find tid ctx_ths = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_context; eauto.
    eapply DSE_sim; eauto.
  Qed.
End ADEQUACY.
