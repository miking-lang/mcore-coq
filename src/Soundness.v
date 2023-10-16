From MCore Require Import Syntax Typing SmallStep Tactics.
From TLC Require Import LibString LibNat LibList LibLogic LibOrder.
Import LibListNotation.


Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Ltac auto_star ::=
    unfolds tvars ;
    unfolds tvar_in ;
    unfolds is_tvar ;
    unfolds vars ;
    unfolds var_in ;
    unfolds is_var ;
    try (rewrites (>> If_l True) in *) ;
    try (rewrites (>> If_r False) in *) ;
    rew_listx in *;
    try solve [ auto with mcore
              | eauto with mcore
              | intuition eauto with mcore].

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

    Lemma ok_kind_strengthen_vars :
      forall G1 G2 ty' k,
        ok_kind (G1 ++ Bvar ty' :: G2) k ->
        ok_kind (G1 ++ G2) k.
    Proof. introv k_wf. induction* k_wf. Qed.

    Lemma ok_kind_strengthen_tvars :
      forall G1 G2 k' k,
        ok_kind (G1 ++ G2) k ->
        ok_kind (G1 ++ Btvar k' :: G2) k.
    Proof. introv k_wf. induction* k_wf. Qed.

    Lemma ok_type_strengthen_vars :
      forall G1 G2 ty' ty k,
        ok_type (G1 ++ Bvar ty' :: G2) ty k ->
        ok_type (G1 ++ G2) ty k.
    Proof.
      introv tykind.
      remember (G1 ++ Bvar ty' :: G2) as Gamma eqn:HGamma.
      gen G1.
      induction tykind ; intros ; subst* ; constructor*.
      { Case "TyAll". applys* IHtykind (Btvar k :: G1). }
    Qed.

    Definition ty_shift_env Gamma :=
      fold_right
        (fun b bs =>
           match b with
           | Bvar ty => Bvar (ty_shift_gen ty (length (tvars bs)))
           | _ => b
           end :: bs)
        [ ] Gamma.

    Lemma ty_shift_env_length :
      forall Gamma,
        length (tvars (ty_shift_env Gamma)) = length (tvars Gamma).
    Proof. Admitted.

    Lemma ok_kind_strengthen_shift :
      forall G1 G2 k,
        ok_kind (G1 ++ G2) k ->
        ok_kind (ty_shift_env G1 ++ G2) k.
    Proof. Admitted.


    Lemma ok_type_weaken_tvars_gen :
      forall G1 G2 k' ty k,
        ok_type (G1 ++ G2) ty k ->
        ok_type (ty_shift_env G1 ++ k' :: G2) (ty_shift_gen ty (length (tvars G1))) k.
    Proof. Admitted.

    (* Lemma ok_type_tvars_weaken : *)
    (*   forall Gamma k' ty k, *)
    (*     ok_type Gamma ty k -> *)
    (*     ok_type (Gamma <| tvars ::= fun tvs => k' :: tvs |>) (ty_shift ty) k. *)
    (* Proof. Admitted. *)

    (* Lemma shift_subst_comm : *)
    (*   forall t1  *)

    Lemma ok_term_weaken_tvars_gen :
      forall G1 G2 k t ty,
        ok_term (G1 ++ G2) t ty ->
        ok_term (ty_shift_env G1 ++ Btvar k :: G2)
                (tm_ty_shift_gen t (length (tvars G1)))
                (ty_shift_gen ty (length (tvars G1))).
    Proof.
      introv ttype.
      remember (G1 ++ G2) as Gamma eqn:HGamma.
      gen G1.
      induction ttype ; intros ; subst*.
      { Case "TmVar". admit. }
      { Case "TmLam". constructor.
        applys* ok_type_weaken_tvars_gen.
        applys_eq* (IHttype (Bvar ty1 :: G1)). unfolds* ty_shift_env. rewrite* ty_shift_env_length.
        auto_star. auto_star. }
      { Case "TmTyLam". constructor.
        applys ok_kind_strengthen_tvars.
        applys* ok_kind_strengthen_shift.
        applys_eq* (IHttype (Btvar k0 :: G1)) ; rew_listx*. }
      { Case "TmTyApp". unfold ty_shift_gen.  constructor.
      }
    Admitted.

    (* Lemma ok_term_tvars_weaken : *)
    (*   forall Gamma k t ty, *)
    (*     ok_term Gamma t ty -> *)
    (*     ok_term (Gamma <| tvars ::= fun tvs => k :: tvs |>) (tm_ty_shift t) (ty_shift ty). *)
    (* Proof. Admitted. *)

    Lemma ok_term_weaken_vars :
      forall Gamma ty' t ty,
        ok_term Gamma t ty ->
        ok_term (Bvar ty' :: Gamma) (tm_shift t) ty.
    Proof. Admitted.

    Lemma tm_subst_gen_preservation :
      forall G1 G2 t ty t' ty',
        ok_term (G1 ++ Bvar ty' :: G2) t ty ->
        ok_term (G1 ++ G2) t' ty' ->
        ok_term (G1 ++ G2) (tm_subst_gen t (length (vars G1)) t') ty.
    Proof.
      introv ttype.
      remember (G1 ++ Bvar ty1 :: G2) as Gamma eqn:HGamma.
      gen t' ty1 G1.
      induction ttype ; intros ; subst*.
      { Case "TmVar". with_hyp (Nth _ _ _) as Hvar.
        unfold tm_subst_gen.
        lets [ in_vs1 | (m & Heqm & in_vs2') ] : Nth_app_inv Hvar.
        { lets Hlt : Nth_inbound in_vs1. rewrites (>> If_l Hlt).
          constructor*. applys* Nth_app_l. }
        { subst. assert (nlt : ~(length (vars G1) + m < length (vars G1))). nat_math.
          rewrites* (>> If_r nlt).
          lets [ (Heq0 & Heq) | (m' & Heqm' & in_vs2) ] : Nth_cons_inv in_vs2' ; subst.
          { inverts Heq. rewrites* (>> If_l plus_zero_r). }
          { rew_nat. assert (neq : S (length (vars G1) + m') <> length (vars G1)). nat_math.
            rewrites (>> If_r neq). rewrite Nat.add_comm.
            constructor*. applys Nth_app_r in_vs2. } } }
      { Case "TmLam". constructors*.
        applys* ok_type_strengthen_vars ty0.
        applys_eq* (IHttype (tm_shift t') ty0 (Bvar ty1 :: G1)). unfolds* is_var.
        applys_eq* (ok_term_weaken_vars (G1 ++ G2) ty1). }
      { Case "TmTyLam". constructors*.
        applys* ok_kind_strengthen_vars ty1. folds (tm_subst_gen t (length (filter is_var G1)) (tm_ty_shift t')).
        applys_eq* (IHttype (tm_ty_shift t') (Btvar k :: G1) (ty_shift ty1)).
        applys* ok_term_tvars_weaken (Gamma <| vars := vs1 ++ vs2 |> <| tvars := tvs |>). }
      { Case "TmTyApp". constructors*.
        applys* ok_type_ignores_vars (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>). }
    Qed.

    Lemma tm_subst_preservation :
      forall Gamma t t' ty1 ty2,
        ok_term (Bvar ty1 :: Gamma) t ty2 ->
        ok_term Gamma t' ty1 ->
        ok_term Gamma (tm_subst t t') ty2.
    Proof. Admitted.

    Lemma tm_ty_subst_preservation :
      forall Gamma t ty ty' k,
        ok_term (Btvar k :: Gamma) t ty' ->
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
