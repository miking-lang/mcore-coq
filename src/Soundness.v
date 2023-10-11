From MCore Require Import Syntax Typing SmallStep Tactics.
From TLC Require Import LibString LibList.
From RecordUpdate Require Import RecordUpdate.

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
      ; try (left; constructor).
      - Case "TmVar". subst. with_hyp (var_in _ _ _) as H. inversion H.
      - Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHttype1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHttype2.
        inverts* Hval1. inverts* ttype1.
      - Case "TmTyApp". right.
        forwards* [Hval | (t' & Hstep)]: IHttype.
        inverts* Hval. inverts ttype.
    Qed.

    Lemma tm_subst_gen_preservation :
      forall vs1 vs2 Gamma t t' ty1 ty2,
        ok_term (Gamma <| vars := vs1 ++ ty1 :: vs2 |>) t ty2 ->
        ok_term (Gamma <| vars := vs1 ++ vs2 |>) t' ty1 ->
        ok_term (Gamma <| vars := vs1 ++ vs2 |>) (tm_subst_gen t (length vs1) t') ty2.
    Proof. Admitted.

    Lemma tm_subst_preservation :
      forall Gamma t t' ty1 ty2,
        ok_term (Gamma <| vars ::= (fun vs => ty1 :: vs) |>) t ty2 ->
        ok_term Gamma t' ty1 ->
        ok_term Gamma (tm_subst t t') ty2.
    Proof.
      intros. applys_eq (tm_subst_gen_preservation nil Gamma.(vars) Gamma t t' ty1) ; destruct* Gamma.
    Qed.

    Lemma tm_ty_subst_preservation :
      forall Gamma t ty ty' k,
        ok_term (Gamma <| tvars ::= fun tvs => k :: tvs |>) t ty' ->
        ok_type Gamma ty k ->
        ok_term Gamma (tm_ty_subst t ty) (ty_subst ty' ty).
    Admitted.

    Theorem preservation :
      forall Gamma t t' ty,
        ok_term Gamma t ty ->
        eval_step t t' ->
        ok_term Gamma t' ty.
    Proof.
      introv ttype tstep.
      gen t'.
      induction ttype ; intros ; inverts tstep
      ; try (with_hyp (is_context _) as ctx ; with_hyp (_ = _) as eq
             ; inverts ctx ; inverts* eq).
      - Case "TmApp". inverts ttype1. applys* tm_subst_preservation.
      - Case "TmTyApp". inverts ttype. applys* tm_ty_subst_preservation.
    Qed.
  End Soundness.
End Soundness.
