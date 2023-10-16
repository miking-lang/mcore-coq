From MCore Require Import Syntax Typing SmallStep Tactics.
From TLC Require Import LibString LibNat LibList LibLogic LibOrder.
Import LibListNotation.


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
      { Case "TmFVar". subst. with_hyp (var_in _ _ _) as Hvar. inversion Hvar. }
      { Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHttype1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHttype2.
        inverts* Hval1. inverts* ttype1. }
      { Case "TmTyApp". right.
        forwards* [Hval | (t' & Hstep)]: IHttype.
        inverts* Hval. inverts ttype. }
    Qed.

    (* Lemma ok_kind_strengthen_vars : *)
    (*   forall G1 G2 ty' k, *)
    (*     ok_kind (G1 ++ Bvar ty' :: G2) k -> *)
    (*     ok_kind (G1 ++ G2) k. *)
    (* Proof. introv k_wf. induction* k_wf. Qed. *)

    (* Lemma ok_kind_strengthen_tvars : *)
    (*   forall G1 G2 k' k, *)
    (*     ok_kind (G1 ++ G2) k -> *)
    (*     ok_kind (G1 ++ Btvar k' :: G2) k. *)
    (* Proof. introv k_wf. induction* k_wf. Qed. *)

    (* Lemma ok_type_strengthen_vars : *)
    (*   forall G1 G2 ty' ty k, *)
    (*     ok_type (G1 ++ Bvar ty' :: G2) ty k -> *)
    (*     ok_type (G1 ++ G2) ty k. *)
    (* Proof. *)
    (*   introv tykind. *)
    (*   remember (G1 ++ Bvar ty' :: G2) as Gamma eqn:HGamma. *)
    (*   gen G1. *)
    (*   induction tykind ; intros ; subst* ; constructor*. *)
    (*   { Case "TyAll". applys* IHtykind (Btvar k :: G1). } *)
    (* Qed. *)

    (* Definition ty_shift_env Gamma := *)
    (*   fold_right *)
    (*     (fun b bs => *)
    (*        match b with *)
    (*        | Bvar ty => Bvar (ty_shift_gen ty (length (tvars bs))) *)
    (*        | _ => b *)
    (*        end :: bs) *)
    (*     [ ] Gamma. *)

    (* Lemma ty_shift_env_length : *)
    (*   forall Gamma, *)
    (*     length (tvars (ty_shift_env Gamma)) = length (tvars Gamma). *)
    (* Proof. Admitted. *)

    (* Lemma ok_kind_strengthen_shift : *)
    (*   forall G1 G2 k, *)
    (*     ok_kind (G1 ++ G2) k -> *)
    (*     ok_kind (ty_shift_env G1 ++ G2) k. *)
    (* Proof. Admitted. *)


    (* Lemma ok_type_weaken_tvars_gen : *)
    (*   forall G1 G2 k' ty k, *)
    (*     ok_type (G1 ++ G2) ty k -> *)
    (*     ok_type (ty_shift_env G1 ++ k' :: G2) (ty_shift_gen ty (length (tvars G1))) k. *)
    (* Proof. Admitted. *)

    (* Lemma ok_type_tvars_weaken : *)
    (*   forall Gamma k' ty k, *)
    (*     ok_type Gamma ty k -> *)
    (*     ok_type (Gamma <| tvars ::= fun tvs => k' :: tvs |>) (ty_shift ty) k. *)
    (* Proof. Admitted. *)

    (* Lemma shift_subst_comm : *)
    (*   forall t1  *)

    (* Lemma ok_term_weaken_tvars_gen : *)
    (*   forall G1 G2 k t ty, *)
    (*     ok_term (G1 ++ G2) t ty -> *)
    (*     ok_term (ty_shift_env G1 ++ Btvar k :: G2) *)
    (*             (tm_ty_shift_gen t (length (tvars G1))) *)
    (*             (ty_shift_gen ty (length (tvars G1))). *)
    (* Proof. *)
    (*   introv ttype. *)
    (*   remember (G1 ++ G2) as Gamma eqn:HGamma. *)
    (*   gen G1. *)
    (*   induction ttype ; intros ; subst*. *)
    (*   { Case "TmVar". admit. } *)
    (*   { Case "TmLam". constructor. *)
    (*     applys* ok_type_weaken_tvars_gen. *)
    (*     applys_eq* (IHttype (Bvar ty1 :: G1)). unfolds* ty_shift_env. rewrite* ty_shift_env_length. *)
    (*     auto_star. auto_star. } *)
    (*   { Case "TmTyLam". constructor. *)
    (*     applys ok_kind_strengthen_tvars. *)
    (*     applys* ok_kind_strengthen_shift. *)
    (*     applys_eq* (IHttype (Btvar k0 :: G1)) ; rew_listx*. } *)
    (*   { Case "TmTyApp". unfold ty_shift_gen.  constructor. *)
    (*   } *)
    (* Admitted. *)

    (* Lemma ok_term_tvars_weaken : *)
    (*   forall Gamma k t ty, *)
    (*     ok_term Gamma t ty -> *)
    (*     ok_term (Gamma <| tvars ::= fun tvs => k :: tvs |>) (tm_ty_shift t) (ty_shift ty). *)
    (* Proof. Admitted. *)

    (* Lemma ok_term_weaken_vars : *)
    (*   forall Gamma ty' t ty, *)
    (*     ok_term Gamma t ty -> *)
    (*     ok_term (Bvar ty' :: Gamma) (tm_shift t) ty. *)
    (* Proof. Admitted. *)

    (* Lemma tm_subst_gen_preservation : *)
    (*   forall G1 G2 t ty t' ty', *)
    (*     ok_term (G1 ++ Bvar ty' :: G2) t ty -> *)
    (*     ok_term (G1 ++ G2) t' ty' -> *)
    (*     ok_term (G1 ++ G2) (tm_subst_gen t (length (vars G1)) t') ty. *)
    (* Proof. *)
    (*   introv ttype. *)
    (*   remember (G1 ++ Bvar ty1 :: G2) as Gamma eqn:HGamma. *)
    (*   gen t' ty1 G1. *)
    (*   induction ttype ; intros ; subst*. *)
    (*   { Case "TmVar". with_hyp (Nth _ _ _) as Hvar. *)
    (*     unfold tm_subst_gen. *)
    (*     lets [ in_vs1 | (m & Heqm & in_vs2') ] : Nth_app_inv Hvar. *)
    (*     { lets Hlt : Nth_inbound in_vs1. rewrites (>> If_l Hlt). *)
    (*       constructor*. applys* Nth_app_l. } *)
    (*     { subst. assert (nlt : ~(length (vars G1) + m < length (vars G1))). nat_math. *)
    (*       rewrites* (>> If_r nlt). *)
    (*       lets [ (Heq0 & Heq) | (m' & Heqm' & in_vs2) ] : Nth_cons_inv in_vs2' ; subst. *)
    (*       { inverts Heq. rewrites* (>> If_l plus_zero_r). } *)
    (*       { rew_nat. assert (neq : S (length (vars G1) + m') <> length (vars G1)). nat_math. *)
    (*         rewrites (>> If_r neq). rewrite Nat.add_comm. *)
    (*         constructor*. applys Nth_app_r in_vs2. } } } *)
    (*   { Case "TmLam". constructors*. *)
    (*     applys* ok_type_strengthen_vars ty0. *)
    (*     applys_eq* (IHttype (tm_shift t') ty0 (Bvar ty1 :: G1)). unfolds* is_var. *)
    (*     applys_eq* (ok_term_weaken_vars (G1 ++ G2) ty1). } *)
    (*   { Case "TmTyLam". constructors*. *)
    (*     applys* ok_kind_strengthen_vars ty1. folds (tm_subst_gen t (length (filter is_var G1)) (tm_ty_shift t')). *)
    (*     applys_eq* (IHttype (tm_ty_shift t') (Btvar k :: G1) (ty_shift ty1)). *)
    (*     applys* ok_term_tvars_weaken (Gamma <| vars := vs1 ++ vs2 |> <| tvars := tvs |>). } *)
    (*   { Case "TmTyApp". constructors*. *)
    (*     applys* ok_type_ignores_vars (Gamma <| vars := vs1 ++ ty1 :: vs2 |> <| tvars := tvs |>). } *)
    (* Qed. *)

    Lemma tm_freshen_preservation :
      forall Gamma t ty ty',
        ok_term Gamma t ty ->
        ok_term (BindVar ty' :: Gamma) (tm_freshen t 0) ty.
    Proof. Admitted.

    Lemma tm_ty_freshen_preservation :
      forall Gamma t ty k',
        ok_term Gamma t ty ->
        ok_term (BindTvar k' :: Gamma) (tm_ty_freshen t 0) ty.
    Proof. Admitted.

    Lemma tm_open_subst_comm :
      forall t n t',
        tm_lc t' ->
        tm_open (tm_subst t n t') = tm_subst (tm_open t) (S n) (tm_freshen t' 0).
    Proof. Admitted.

    Lemma tm_ty_open_subst_comm :
      forall t n t',
        tm_lc t' ->
        tm_ty_open (tm_subst t n t') = tm_subst (tm_ty_open t) n (tm_ty_freshen t' 0).
    Proof. Admitted.

    Lemma tm_open_defreshen_comm :
      forall t n,
        tm_open (tm_defreshen t n) = tm_defreshen (tm_open t) (S n).
    Proof. Admitted.

    Lemma tm_ty_open_defreshen_comm :
      forall t n,
        tm_ty_open (tm_defreshen t n) = tm_defreshen (tm_ty_open t) n.
    Proof. Admitted.

    Lemma ok_type_lct :
      forall Gamma ty k,
        ok_type Gamma ty k ->
        ty_lc ty.
    Proof. introv tykind. induction* tykind. Qed.

    Lemma ok_env_lct :
      forall Gamma ty x,
        ok_env Gamma ->
        var_in x (Some ty) (vars Gamma) ->
        ty_lc ty.
    Proof.
      introv Henv. gen x.
      induction* Gamma ; intros ; with_hyp (var_in _ _ _) as Hvar. inverts Hvar.
      destruct a; rew_mcore in *; inverts* Henv ; unfold var_in in Hvar.
      { lets [ (Heq0 & Heqty) | (m & Heqm & in_Gamma) ] : Nth_cons_inv Hvar ; subst.
        { inverts Heqty. apply* ok_type_lct. }
        { apply* IHGamma. } }
      { lets [ (Heq0 & Heqty) | (m & Heqm & in_Gamma) ] : Nth_cons_inv Hvar ; subst.
        { inverts Heqty. }
        { apply* IHGamma. } }
    Qed.

    Lemma ok_term_lct :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        ty_lc ty.
    Proof.
      introv ttype. induction* ttype.
      { Case "TmVar". apply* ok_env_lct. }
      { Case "TmLam". constructor. with_hyp (ok_type _ _ _) as Htyp. applys ok_type_lct Htyp. auto. }
      { Case "TmApp". inverts* IHttype1. }
      { Case "TmTyApp". inverts* IHttype. (* Lemma here *) }

    Lemma ok_term_lc :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        tm_lc t.
    Proof.
      introv ttype. induction* ttype.
      { Case "TmLam". constructor*. admit. } Admitted.

    Lemma ok_data_strengthen_var :
      forall G1 G2 ty' d,
        ok_data (G1 ++ BindVar (Some ty') :: G2) d ->
        ok_data (G1 ++ BindVar None :: G2) d.
    Proof. Admitted.

    Lemma ok_kind_strengthen_var :
      forall G1 G2 ty' k,
        ok_kind (G1 ++ BindVar (Some ty') :: G2) k ->
        ok_kind (G1 ++ BindVar None :: G2) k.
    Proof. Admitted.

    Lemma ok_type_strengthen_var :
      forall G1 G2 ty' ty k,
        ok_type (G1 ++ BindVar (Some ty') :: G2) ty k ->
        ok_type (G1 ++ BindVar None :: G2) ty k.
    Proof. Admitted.

    Lemma ok_env_strengthen_var :
      forall G1 G2 ty,
        ok_env (G1 ++ BindVar (Some ty) :: G2) ->
        ok_env (G1 ++ BindVar None :: G2).
    Proof.
      introv Henv. induction* G1 ; rew_list in *. inverts* Henv.
      destruct* a ; inverts* Henv. constructor*.
      apply* ok_data_strengthen_var. apply* ok_type_strengthen_var. unfolds tnames. rew_listx in *.
      unfold is_tname in *. rew_mcore* in *.
      constructor. apply* IHG1. apply* ok_kind_strengthen_var.
      constructor. apply* IHG1. apply* ok_type_strengthen_var.
    Qed.

    Lemma ok_data_drop_var :
      forall G1 G2 d,
        ok_data (G1 ++ BindVar None :: G2) d ->
        ok_data (G1 ++ G2) d.
    Proof. Admitted.

    Lemma ok_kind_drop_var :
      forall G1 G2 k,
        ok_kind (G1 ++ BindVar None :: G2) k ->
        ok_kind (G1 ++ G2) k.
    Proof. Admitted.

    Lemma ok_type_drop_var :
      forall G1 G2 ty k,
        ok_type (G1 ++ BindVar None :: G2) ty k ->
        ok_type (G1 ++ G2) ty k.
    Proof. Admitted.

    Lemma ok_env_drop_var :
      forall G1 G2,
        ok_env (G1 ++ BindVar None :: G2) ->
        ok_env (G1 ++ G2).
    Proof.
      introv Henv. induction* G1 ; rew_list in *. inverts* Henv.
      destruct* a ; inverts* Henv. constructor*.
      apply* ok_data_drop_var. apply* ok_type_drop_var. unfolds tnames. rew_listx in *.
      unfold is_tname in *. rew_mcore* in *.
      constructor. apply* IHG1. apply* ok_kind_drop_var.
      constructor. apply* IHG1. apply* ok_type_drop_var.
    Qed.

    Lemma ok_term_drop_var :
      forall G1 G2 t ty,
        ok_term (G1 ++ BindVar None :: G2) t ty ->
        ok_term (G1 ++ G2) (tm_defreshen t (length (vars G1))) ty.
    Proof.
      introv ttype.
      remember (G1 ++ BindVar None :: G2) as Gamma eqn:HGamma.
      gen G1.
      induction ttype ; intros ; subst*.
      { Case "TmFVar". with_hyp (var_in _ _ _) as Hvar. rew_mcore in Hvar. unfold var_in in Hvar.
        unfold tm_defreshen.
        lets [ in_vs1 | (m' & Heqm' & in_vs2') ] : Nth_app_inv Hvar.
        { lets Hlt : Nth_inbound in_vs1. assert (Hnge : ~(x > length (vars G1))). apply* lt_gt_false.
          rewrites (>> If_r Hnge). constructor. apply* ok_env_drop_var. unfold var_in. rew_mcore.
          applys* Nth_app_l. }
        { lets [ (Heq0 & Heqty) | (m & Heqm & in_vs2) ] : Nth_cons_inv in_vs2' ; subst.
          { inverts Heqty. }
          { rew_nat. assert (Hge : S (length (vars G1) + m) > length (vars G1)). nat_math.
            rewrites (>> If_l Hge).
            constructor. apply* ok_env_drop_var. unfold var_in. rew_mcore.
            applys_eq* (>> Nth_app_r in_vs2). nat_math. } } }
      { Case "TmLam". constructor. apply* ok_type_drop_var.
        rewrite tm_open_defreshen_comm.
        applys_eq* (IHttype (BindVar (Some ty1) :: G1)). rew_mcore*. }
      { Case "TmTyLam". constructor. apply* ok_kind_drop_var.
        rewrite tm_ty_open_defreshen_comm.
        applys_eq* (IHttype (BindTvar (Some k) :: G1)). rew_mcore*. }
      { Case "TmTyApp". constructors*. apply* ok_type_drop_var. }
    Qed.

    Lemma tm_subst_preservation_gen :
      forall G1 G2 t t' ty1 ty2,
        ok_term (G1 ++ BindVar (Some ty1) :: G2) t ty2 ->
        ok_term (G1 ++ BindVar None :: G2) t' ty1 ->
        ok_term (G1 ++ BindVar None :: G2) (tm_subst t (length (vars G1)) t') ty2.
    Proof.
      introv ttype.
      remember (G1 ++ BindVar (Some ty1) :: G2) as Gamma eqn:HGamma.
      gen t' G1.
      induction ttype ; intros ; subst*.
      { Case "TmFVar".
        with_hyp (var_in _ _ _) as Hvar. rew_mcore in Hvar. unfold var_in in Hvar.
        unfold tm_subst.
        lets [ in_vs1 | (m' & Heqm' & in_vs2') ] : Nth_app_inv Hvar.
        { lets Hlt : Nth_inbound in_vs1. assert (Hneq : x <> length (vars G1)). nat_math.
          rewrites (>> If_r Hneq). constructor. apply* ok_env_strengthen_var. unfold var_in. rew_mcore.
          applys* Nth_app_l. }
        { lets [ (Heq0 & Heqty) | (m & Heqm & in_vs2) ] : Nth_cons_inv in_vs2'.
          { inverts* Heqty. assert (Heq : x = length (vars G1)). nat_math.
            rewrites* (>> If_l Heq). }
          { assert (Hneq : x <> length (vars G1)). nat_math.
            rewrites (>> If_r Hneq). constructor. apply* ok_env_strengthen_var. unfold var_in. rew_mcore.
            applys_eq* (>> Nth_app_r (vars G1 ++ [BindVar None]) in_vs2) ; rew_list~. nat_math. } } }
      { Case "TmLam". constructor. applys* ok_type_strengthen_var ty1.
        rewrite tm_open_subst_comm.
        applys_eq* (IHttype (tm_freshen t' 0) (BindVar (Some ty0) :: G1)). rew_mcore*.
        rew_list. applys* tm_freshen_preservation. applys* ok_term_lc. }
      { Case "TmTyLam". constructor. applys* ok_kind_strengthen_var ty1.
        rewrite tm_ty_open_subst_comm.
        applys_eq* (IHttype (tm_ty_freshen t' 0) (BindTvar (Some k) :: G1)). rew_mcore*.
        rew_list. applys* tm_ty_freshen_preservation. applys* ok_term_lc. }
      { Case "TmTyApp". constructors*. applys* ok_type_strengthen_var ty1. }
    Qed.

    Lemma tm_ty_subst_preservation :
      forall Gamma t ty ty' k,
        ok_term (BindTvar (Some k) :: Gamma) (tm_ty_open t) (ty_open ty) ->
        ok_type Gamma ty' k ->
        ok_term Gamma (tm_ty_bsubst t 0 ty') (ty_bsubst ty 0 ty').
    Proof. Admitted.

    Lemma tm_subst_preservation :
      forall Gamma t t' ty1 ty2,
        ok_term (BindVar (Some ty1) :: Gamma) t ty2 ->
        ok_term Gamma t' ty1 ->
        ok_term Gamma (tm_defreshen (tm_subst t 0 (tm_freshen t' 0)) 0) ty2.
    Proof. Admitted.

    Lemma tm_bsubst_preservation :
      forall Gamma t t' ty1 ty2,
        ok_term (BindVar (Some ty1) :: Gamma) (tm_open t) ty2 ->
        ok_term Gamma t' ty1 ->
        ok_term Gamma (tm_bsubst t 0 t') ty2.
    Proof. Admitted.

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
      { Case "TmApp". inverts ttype1. applys* tm_bsubst_preservation. }
      { Case "TmTyApp". inverts ttype. applys* tm_ty_subst_preservation. }
    Qed.
  End Soundness.
End Soundness.
