From MCore Require Import Syntax Typing SmallStep Util.
From TLC Require Import LibTactics LibString.

Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Module Soundness (PC : PATCHECK) (M : MATCH).
    Module Typing := Typing PC.
    Module SmallStep := SmallStep M.
    Import Typing SmallStep.

    Theorem progress :
      forall t ty,
        ok_term empty_env t ty ->
        is_value t \/ exists t', eval_step t t'.
    Proof.
      introv ttype.
      remember empty_env as Gamma eqn:HGamma.
      induction ttype
        as [ ??? var_in
           | | ??? t1 t2 ttype1 IH1 ? IH2
           | | ??? ty2 t ? IH ]
      ; try (left ; constructor).
      - Case "TmVar". subst. inversion var_in.
      - Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IH1.
        forwards* [Hval2 | (t2' & Hstep2)]: IH2.
        * inverts* Hval1. inverts ttype1.
        * exists (TmApp t1 t2'). apply (ECong (CAppR t1 Hval1) Hstep2).
        * exists (TmApp t1' t2). apply (ECong (CAppL t2) Hstep1).
      - Case "TmTyApp". right.
        forwards* [Hval | (t' & Hstep)]: IH.
        * inverts* Hval. inverts ttype.
        * exists (TmTyApp t' ty2). apply (ECong (CTyApp ty2) Hstep).
    Qed.

    Theorem preservation :
      forall Gamma t t' ty,
        ok_term Gamma t ty ->
        eval_step t t' ->
        ok_term Gamma t' ty.
    Proof.
      intros Gamma t t' ty ttype tstep.
      gen t'.
      induction ttype
        as [| | ? ? ? t1 t2 ttype1 IH1 ttype2 IH2
            | | ? ? ? ty2 t ? IH ]
      ; intros
      ; try (inverts tstep ; with_hyp eval_context as ctx ; destruct ctx ; discriminate).
      - Case "TmApp". admit.
      - Case "TmTyApp". admit.
    Admitted.
  End Soundness.
End Soundness.
