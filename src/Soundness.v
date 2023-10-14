From MCore Require Import Syntax Typing SmallStep Tactics.
From TLC Require Import LibString LibNat LibList LibLogic LibOrder.
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
      { Case "TmVar". subst. with_hyp (var_in _ _ _) as H. inversion H. }
      { Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHttype1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHttype2.
        inverts* Hval1. inverts* ttype1. }
      { Case "TmTyApp". right.
        forwards* [Hval | (t' & Hstep)]: IHttype.
        inverts* Hval. inverts ttype. }
    Qed.

    Lemma ok_kind_ignores_vars :
      forall Gamma vs k,
        ok_kind Gamma k ->
        ok_kind (Gamma <| vars := vs |>) k.
    Proof. Admitted.

    Lemma ok_type_ignores_vars :
      forall Gamma vs ty k,
        ok_type Gamma ty k ->
        ok_type (Gamma <| vars := vs |>) ty k.
    Proof. Admitted.

    Lemma ok_term_tvars_weaken :
      forall Gamma k t ty,
        ok_term Gamma t ty ->
        ok_term (Gamma <| tvars ::= fun tvs => k :: tvs |>) (tm_ty_shift t) ty.
    Proof. Admitted.

    Lemma ok_term_vars_weaken :
      forall Gamma ty' t ty,
        ok_term Gamma t ty ->
        ok_term (Gamma <| vars ::= fun vs => ty' :: vs |>) (tm_shift t) ty.
    Proof. Admitted.

    Lemma tm_subst_gen_preservation :
      forall vs1 vs2 tvs Gamma t t' ty1 ty2,
        ok_term (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>) t ty2 ->
        ok_term (Gamma <| vars := vs1 ++ vs2 |> <| tvars := tvs |>) t' ty1 ->
        ok_term (Gamma <| vars := vs1 ++ vs2 |> <| tvars := tvs |>) (tm_subst_gen t (length vs1) t') ty2.
    Proof.
      introv ttype ttype'.
      remember (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>) as Gamma' eqn:HGamma.
      gen t' vs1 tvs.
      induction* ttype ; intros ; subst.
      { Case "TmVar". with_hyp (var_in _ _ _) as Hvar. unfold tm_subst_gen.
        lets [ in_vs1 | (m & Heqm & in_vs2') ] : Nth_app_inv Hvar.
        { lets Hlt : Nth_inbound in_vs1. rewrites (>> If_l Hlt).
          constructor. applys* Nth_app_l. }
        { subst. assert (nlt : ~(length vs1 + m < length vs1)). nat_math.
          rewrites (>> If_r nlt).
          lets [ (Heq0 & Heq) | (m' & Heqm' & in_vs2) ] : Nth_cons_inv in_vs2' ; subst.
          { rewrites* (>> If_l plus_zero_r). }
          { rew_nat. assert (neq : ~(S (length vs1 + m') = length vs1)). nat_math.
            rewrites (>> If_r neq). rewrite Nat.add_comm.
            constructor. applys Nth_app_r in_vs2. } } }
      { Case "TmLam". constructors*.
        applys* ok_type_ignores_vars (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>).
        folds (tm_subst_gen t (S (length vs1)) (tm_shift t')).
        applys* IHttype (tm_shift t') (ty0 :: vs1).
        applys_eq* (ok_term_vars_weaken (Gamma <| vars := vs1 ++ vs2 |> <| tvars := tvs |>) ty0). }
      { Case "TmTyLam". constructors*.
        applys* ok_kind_ignores_vars (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>).
        applys* IHttype. applys* ok_term_tvars_weaken (Gamma <| vars := vs1 ++ vs2 |> <| tvars := tvs |>). }
      { Case "TmTyApp". constructors*.
        applys* ok_type_ignores_vars (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>). }
    Qed.

    Lemma tm_subst_preservation :
      forall Gamma t t' ty1 ty2,
        ok_term (Gamma <| vars ::= (fun vs => ty1 :: vs) |>) t ty2 ->
        ok_term Gamma t' ty1 ->
        ok_term Gamma (tm_subst t t') ty2.
    Proof.
      intros. applys_eq* (tm_subst_gen_preservation nil Gamma.(vars) Gamma.(tvars) Gamma t t' ty1) ;
        destruct* Gamma.
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
      { Case "TmApp". inverts ttype1. applys* tm_subst_preservation. }
      { Case "TmTyApp". inverts ttype. applys* tm_ty_subst_preservation. }
    Qed.
  End Soundness.
End Soundness.
