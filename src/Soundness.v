From MCore Require Import Syntax Typing SmallStep Tactics.
From TLC Require Import LibString LibList LibNat.
Import LibListNotation.

Open Scope nat_scope.

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
      induction ttype ; subst
      ; try (left; constructor).
      { Case "TmFVar". with_hyp (var_in _ _ _) as Hvar. inversion Hvar. }
      { Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHttype1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHttype2.
        inverts* Hval1. inverts* ttype1. }
      { Case "TmTyApp". right.
        forwards* [Hval | (t' & Hstep)]: IHttype.
        inverts* Hval. inverts ttype. }
    Qed.

    Lemma tm_defreshen_freshen : forall t x, tm_defreshen (tm_freshen t x) x = t.
    Proof. intros ; induction t ; simple_math ; simpls ; fequals*. Qed.

    Lemma ty_defreshen_freshen : forall t x, ty_defreshen (ty_freshen t x) x = t.
    Proof. intros ; induction t ; simple_math ; simpls ; fequals*. Qed.

    Lemma tm_freshen_fresh : forall t x, var_fresh x (tm_freshen t x).
    Proof. intros ; unfold var_fresh ; rewrite* tm_defreshen_freshen. Qed.

    Lemma ty_freshen_fresh : forall t x, tvar_fresh x (ty_freshen t x).
    Proof. intros ; unfold tvar_fresh ; rewrite* ty_defreshen_freshen. Qed.

    Lemma var_not_fresh : forall x, ~(var_fresh x (TmFVar x)).
    Proof.
      introv Heq. unfolds var_fresh. simple_math.
      inverts Heq ; nat_math.
    Qed.

    Lemma tvar_not_fresh : forall x, ~(tvar_fresh x (TyFVar x)).
    Proof.
      introv Heq. unfolds tvar_fresh. simple_math.
      inverts Heq ; nat_math.
    Qed.

    Lemma var_neq_fresh : forall x y, x <> y -> var_fresh x (TmFVar y).
    Proof.
      introv Hneq. unfolds. simple_math.
      forwards [ k [ Heq Hle ] ] : Nat.lt_exists_pred x y ; subst ; rew_nat*.
    Qed.

    Lemma tm_subst_fresh : forall t x u, var_fresh x t -> tm_subst t x u = t.
    Proof.
      introv Hfresh. unfolds.
      induction* t ; fequals ; try (injection Hfresh ; auto_star).
      { Case "TmFVar". cases_if*. lets* ? : var_not_fresh v. }
    Qed.

    Lemma tm_freshen_freshen :
      forall t x y,
        x <= y ->
        tm_freshen (tm_freshen t y) x = tm_freshen (tm_freshen t x) (S y).
    Proof. introv Hle ; induction t ; simple_math ; try solve [ simpls ; fequals* ]. Qed.

    Lemma tm_ty_freshen_comm :
      forall t x y,
        tm_ty_freshen (tm_freshen t x) y = tm_freshen (tm_ty_freshen t y) x.
    Proof. intros ; induction t ; simple_math ; simpls ; fequals*. Qed.

    Lemma tm_freshen_subst :
      forall t x y u,
        x <= y ->
        tm_freshen (tm_subst t y u) x =
          tm_subst (tm_freshen t x) (S y) (tm_freshen u x).
    Proof. introv Hge ; induction t ; simple_math ; simpls ; fequals*. Qed.

    Lemma tm_freshen_bsubst : forall t y z u,
        tm_freshen (tm_bsubst t y u) z =
          tm_bsubst (tm_freshen t z) y (tm_freshen u z).
    Proof. induction t ; intros ; simple_math ; simpls ; fequals*. Qed.

    Lemma ty_freshen_bsubst : forall t y z u,
        ty_freshen (ty_bsubst t y u) z =
          ty_bsubst (ty_freshen t z) y (ty_freshen u z).
    Proof. induction t ; intros ; simple_math ; simpls ; fequals*. Qed.

    Lemma tm_ty_freshen_bsubst : forall t y z u,
        tm_freshen (tm_ty_bsubst t y u) z =
          tm_ty_bsubst (tm_freshen t z) y u.
    Proof. induction t ; intros ; simple_math ; simpls ; fequals*. Qed.

    Lemma tm_freshen_lc : forall t x, tm_lc t -> tm_lc (tm_freshen t x).
    Proof.
      introv Hlc. unfold tm_freshen.
      gen x.
      induction Hlc ; intros ; simpls*.
      { Case "TmFVar". case_if*. }
      { Case "TmLam". constructor*. unfolds tm_open.
        rewrite tm_freshen_freshen ; try nat_math.
        assert (Hfv : TmFVar 0 = tm_freshen (TmFVar 0) (S x)) by simple_math.
        rewrite Hfv. rewrite* <- tm_freshen_bsubst. }
      { Case "TmTyLam". constructor*. unfolds tm_ty_open.
        rewrite tm_ty_freshen_comm. rewrite* <- tm_ty_freshen_bsubst. }
    Qed.

    Lemma ty_freshen_lc : forall ty x, ty_lc ty -> ty_lc (ty_freshen ty x).
    Admitted.

    Lemma ty_defreshen_lc : forall ty x, ty_lc ty -> ty_lc (ty_defreshen ty x).
    Admitted.
    (* Proof. *)
    (*   introv Hlc. unfold tm_freshen. *)
    (*   gen n. *)
    (*   induction Hlc ; intros ; simpls*. *)
    (*   { Case "TmFVar". case_if*. } *)
    (*   { Case "TmLam". constructor*. unfolds tm_open. *)
    (*     rewrite tm_freshen_freshen ; try nat_math. *)
    (*     assert (Hfv : TmFVar 0 = tm_freshen (TmFVar 0) (S n)) by simple_math. *)
    (*     rewrite Hfv. rewrite* <- tm_freshen_bsubst. } *)
    (*   { Case "TmTyLam". constructor*. unfolds tm_ty_open. *)
    (*     rewrite tm_ty_freshen_comm. rewrite* <- tm_ty_freshen_bsubst. } *)
    (* Qed. *)

    Lemma ty_lc_subst :
      forall ty1 ty2 x,
        ty_lc ty1 ->
        ty_lc ty2 ->
        ty_lc (ty_subst ty1 x ty2).
    Admitted.

    (* TODO: can freshen be separated out from these lemmas into separate ones? *)
    Lemma ty_bsubst_neq : forall ty x y U1 U2,
        x <> y ->
        ty_bsubst (ty_bsubst (ty_freshen ty 0) x U1) y U2 = ty_bsubst (ty_freshen ty 0) x U1 ->
        ty_bsubst ty y U2 = ty.
    Proof.
      introv Hneq Heq. gen x y.
      induction* ty ; intros ; inverts Heq as Heq' ; simpls ; fequals*.
      { Case "TmBVar". case_if*. case_if* in Heq'. simpls. case_if* in Heq'. }
    Qed.

    Lemma tm_bsubst_neq : forall t x y u1 u2,
        x <> y ->
        tm_bsubst (tm_bsubst (tm_freshen t 0) x u1) y u2 = tm_bsubst (tm_freshen t 0) x u1 ->
        tm_bsubst t y u2 = t.
    Proof.
      introv Hneq Heq. gen x y.
      induction* t ; intros ; inverts Heq as Heq' ; simpls ; fequals*.
      { Case "TmBVar". case_if*. case_if* in Heq'. simpls. case_if* in Heq'. }
    Qed.

    Lemma tm_ty_bsubst_neq : forall t x y ty u,
        tm_bsubst (tm_ty_bsubst (tm_ty_freshen t 0) x ty) y u =
          tm_ty_bsubst (tm_ty_freshen t 0) x ty ->
        tm_bsubst t y u = t.
    Proof.
      introv Heq. gen x y.
      induction* t ; intros ; inverts Heq ; simpls ; fequals*.
    Qed.

    Lemma tm_bsubst_lc : forall t y u, tm_lc t -> tm_bsubst t y u = t.
    Proof.
      introv Hlc. gen y.
      induction Hlc ; intros ; simpls ; fequals*.
      { Case "TmLam". rewrite tm_bsubst_neq with (x := 0) (u1 := TmFVar 0) ; auto. }
      { Case "TmTyLam". rewrite tm_ty_bsubst_neq with (x := 0) (ty := TyFVar 0) ; auto. }
    Qed.

    Lemma tm_subst_bsubst_distr :
      forall x y t u1 u2,
        tm_lc u1 ->
        tm_subst (tm_bsubst t y u2) x u1 =
          tm_bsubst (tm_subst t x u1) y (tm_subst u2 x u1).
    Proof.
      introv Hlc. unfolds. gen y.
      induction t ; intros ; simpls ; fequals*.
      { Case "TmBVar". case_if*. }
      { Case "TmFVar". case_if*. rewrite* tm_bsubst_lc. }
    Qed.

    Lemma tm_subst_intro :
      forall x y t u,
        var_fresh x t ->
        tm_bsubst t y u = tm_subst (tm_bsubst t y (TmFVar x)) x u.
    Proof.
      introv Hfresh. unfolds. gen y.
      induction t ; intros ; simpls ; fequals
      ; try (injection Hfresh ; auto_star).
      { Case "TmBVar". simple_math. }
      { Case "TmFVar". cases_if*. lets* ? : var_not_fresh v. }
    Qed.

    Lemma ty_subst_intro :
      forall x y ty u,
        tvar_fresh x ty ->
        ty_bsubst ty y u = ty_subst (ty_bsubst ty y (TyFVar x)) x u.
    Proof.
      introv Hfresh. unfolds. gen y.
      induction ty ; intros ; simpls ; fequals
      ; try (injection Hfresh ; auto_star).
      { Case "TmBVar". simple_math. }
      { Case "TmFVar". cases_if*. lets* ? : tvar_not_fresh t. }
    Qed.

    Lemma tm_subst_open :
      forall t u,
        tm_bsubst t 0 u = tm_defreshen (tm_subst (tm_open t) 0 (tm_freshen u 0)) 0.
    Proof.
      intros.
      rewrite <- tm_defreshen_freshen with (x := 0) (t := tm_bsubst t 0 u).
      rewrite tm_freshen_bsubst. rewrite* (@tm_subst_intro 0). apply tm_freshen_fresh.
    Qed.

    Lemma ty_subst_open :
      forall ty u,
        ty_bsubst ty 0 u = ty_defreshen (ty_subst (ty_open ty) 0 (ty_freshen u 0)) 0.
    Proof.
      intros.
      rewrite <- ty_defreshen_freshen with (x := 0) (t := ty_bsubst ty 0 u).
      rewrite ty_freshen_bsubst. rewrite* (@ty_subst_intro 0). apply ty_freshen_fresh.
    Qed.

    Lemma tm_bsubst_subst_comm :
      forall t x y z u,
        x <> z ->
        tm_lc u ->
        tm_bsubst (tm_subst t x u) y (TmFVar z) =
          tm_subst (tm_bsubst t y (TmFVar z)) x u.
    Proof.
      introv Hneq Hlc. symmetry.
      applys_eq* tm_subst_bsubst_distr. fequals.
      rewrite* tm_subst_fresh. apply* var_neq_fresh.
    Qed.

    Lemma tm_open_subst_comm :
      forall t x u,
        tm_lc u ->
        tm_open (tm_subst t x u) = tm_subst (tm_open t) (S x) (tm_freshen u 0).
    Proof.
      introv Hlc. unfolds. rewrite tm_freshen_subst. applys* tm_bsubst_subst_comm.
      apply* tm_freshen_lc. nat_math.
    Qed.

    Lemma tm_ty_open_subst_comm :
      forall t x u,
        tm_lc u ->
        tm_ty_open (tm_subst t x u) = tm_subst (tm_ty_open t) x (tm_ty_freshen u 0).
    Proof. Admitted.

    Lemma tm_open_defreshen_comm :
      forall t x,
        tm_open (tm_defreshen t x) = tm_defreshen (tm_open t) (S x).
    Proof. Admitted.

    Lemma tm_ty_open_defreshen_comm :
      forall t x,
        tm_ty_open (tm_defreshen t x) = tm_defreshen (tm_ty_open t) x.
    Proof. Admitted.

    Lemma ok_type_lct :
      forall Gamma ty k,
        ok_type Gamma ty k ->
        ty_lc ty.
    Proof. introv tykind. induction* tykind. Qed.

    Lemma ok_env_type :
      forall G1 G2 ty,
        ok_env (G1 ++ BindVar ty :: G2) ->
        ok_type G2 ty KiType.
    Proof. introv Henv ; induction* G1 ; inverts* Henv. Qed.

    Lemma ok_env_lct :
      forall Gamma x ty,
        ok_env Gamma ->
        var_in x ty (vars Gamma) ->
        ty_lc ty.
    Proof.
      introv Henv Hvar. unfolds vars.
      forwards Hmem : Nth_mem Hvar.
      forwards* [ Hmem' ? ] : mem_filter_inv Hmem.
      forwards [ G1 (G2 & Heq) ] : mem_inv_middle Hmem' ; subst.
      applys ok_type_lct.
      applys* ok_env_type.
    Qed.

    Lemma ok_term_lct :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        ty_lc ty.
    Proof.
      introv ttype. induction* ttype.
      { Case "TmVar". apply* ok_env_lct. }
      { Case "TmLam". constructor*. with_hyp (ok_type _ _ _) as Htyp. applys ok_type_lct Htyp. }
      { Case "TmApp". inverts* IHttype1. }
      { Case "TmTyApp".
        inverts* IHttype.
        rewrite ty_subst_open.
        apply ty_defreshen_lc. apply* ty_lc_subst. apply ty_freshen_lc. apply* ok_type_lct. }
    Qed.

    Lemma ok_term_lc :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        tm_lc t.
    Proof.
      introv ttype. induction* ttype.
      { Case "TmLam". constructor*. applys* ok_type_lct. }
      { Case "TmTyLam". constructor*. applys* ok_type_lct. }
    Qed.

    Lemma ok_data_strengthen_var :
      forall G1 G2 ty' d,
        ok_data (G1 ++ BindVar ty' :: G2) d ->
        ok_data (G1 ++ SkipVar :: G2) d.
    Proof. Admitted.

    Lemma ok_kind_strengthen_var :
      forall G1 G2 ty' k,
        ok_kind (G1 ++ BindVar ty' :: G2) k ->
        ok_kind (G1 ++ SkipVar :: G2) k.
    Proof. Admitted.

    Lemma ok_type_strengthen_var :
      forall G1 G2 ty' ty k,
        ok_type (G1 ++ BindVar ty' :: G2) ty k ->
        ok_type (G1 ++ SkipVar :: G2) ty k.
    Proof. Admitted.

    Lemma ok_env_strengthen_var :
      forall G1 G2 ty,
        ok_env (G1 ++ BindVar ty :: G2) ->
        ok_env (G1 ++ SkipVar :: G2).
    Proof. Admitted.
    (*   introv Henv. induction* G1 ; rew_list in *. inverts* Henv. *)
    (*   destruct* a ; inverts* Henv. constructor*. *)
    (*   apply* ok_data_strengthen_var. apply* ok_type_strengthen_var. unfolds tnames. rew_listx in *. *)
    (*   unfold is_tname in *. rew_env* in *. *)
    (*   constructor. apply* IHG1. apply* ok_kind_strengthen_var. *)
    (*   constructor. apply* IHG1. apply* ok_type_strengthen_var. *)
    (* Qed. *)

    Lemma ok_data_drop_var :
      forall G1 G2 d,
        ok_data (G1 ++ SkipVar :: G2) d ->
        ok_data (G1 ++ G2) d.
    Proof. Admitted.

    Lemma ok_kind_drop_var :
      forall G1 G2 k,
        ok_kind (G1 ++ SkipVar :: G2) k ->
        ok_kind (G1 ++ G2) k.
    Proof. Admitted.

    Lemma ok_type_drop_var :
      forall G1 G2 ty k,
        ok_type (G1 ++ SkipVar :: G2) ty k ->
        ok_type (G1 ++ G2) ty k.
    Proof. Admitted.

    Lemma ok_env_drop_var :
      forall G1 G2,
        ok_env (G1 ++ SkipVar :: G2) ->
        ok_env (G1 ++ G2).
    Proof. Admitted.
    (*   introv Henv. induction* G1 ; rew_list in *. inverts* Henv. *)
    (*   destruct* a ; inverts* Henv. constructor*. *)
    (*   apply* ok_data_drop_var. apply* ok_type_drop_var. unfolds tnames. rew_listx in *. *)
    (*   unfold is_tname in *. rew_env* in *. *)
    (*   constructor. apply* IHG1. apply* ok_kind_drop_var. *)
    (*   constructor. apply* IHG1. apply* ok_type_drop_var. *)
    (* Qed. *)

    Lemma tm_freshen_preservation :
      forall Gamma t ty b,
        is_var b ->
        ok_term Gamma t ty ->
        ok_term (b :: Gamma) (tm_freshen t 0) ty.
    Proof. Admitted.

    Lemma tm_ty_freshen_preservation :
      forall Gamma t ty b,
        is_tvar b ->
        ok_term Gamma t ty ->
        ok_term (b :: Gamma) (tm_ty_freshen t 0) ty.
    Proof. Admitted.

    Lemma ok_term_drop_var :
      forall G1 G2 t ty,
        ok_term (G1 ++ SkipVar :: G2) t ty ->
        ok_term (G1 ++ G2) (tm_defreshen t (length (vars G1))) ty.
    Proof.
      introv ttype.
      remember (G1 ++ SkipVar :: G2) as Gamma eqn:HGamma.
      gen G1.
      induction ttype ; intros ; subst*.
      { Case "TmFVar". with_hyp (var_in _ _ _) as Hvar. rew_env in Hvar. unfold var_in in Hvar.
        unfold tm_defreshen.
        lets [ in_vs1 | (m' & Heqm' & in_vs2') ] : Nth_app_inv Hvar.
        { lets Hlt : Nth_inbound in_vs1. simple_math.
          constructor. apply* ok_env_drop_var. unfold var_in. rew_env.
          applys* Nth_app_l. }
        { lets [ (Heq0 & Heqty) | (m & Heqm & in_vs2) ] : Nth_cons_inv in_vs2' ; subst.
          { inverts Heqty. }
          { simple_math. constructor. apply* ok_env_drop_var. unfold var_in. rew_env.
            applys_eq* (>> Nth_app_r in_vs2). nat_math. } } }
      { Case "TmLam". constructor. apply* ok_type_drop_var.
        rewrite tm_open_defreshen_comm.
        applys_eq* (IHttype (BindVar ty1 :: G1)). rew_env*. }
      { Case "TmTyLam". constructor. apply* ok_kind_drop_var.
        rewrite tm_ty_open_defreshen_comm.
        applys_eq* (IHttype (BindTvar k :: G1)). rew_env*. }
      { Case "TmTyApp". constructors*. apply* ok_type_drop_var. }
    Qed.

    Lemma tm_subst_preservation :
      forall G1 G2 t t' ty1 ty2,
        ok_term (G1 ++ BindVar ty1 :: G2) t ty2 ->
        ok_term (G1 ++ SkipVar :: G2) t' ty1 ->
        ok_term (G1 ++ SkipVar :: G2) (tm_subst t (length (vars G1)) t') ty2.
    Proof.
      introv ttype.
      remember (G1 ++ BindVar ty1 :: G2) as Gamma eqn:HGamma.
      gen t' G1.
      induction ttype ; intros ; subst*.
      { Case "TmFVar".
        with_hyp (var_in _ _ _) as Hvar. rew_env in Hvar. unfold var_in in Hvar.
        unfold tm_subst.
        lets [ in_vs1 | (m' & Heqm' & in_vs2') ] : Nth_app_inv Hvar.
        { lets Hlt : Nth_inbound in_vs1. simple_math.
          constructor. apply* ok_env_strengthen_var. unfold var_in. rew_env.
          applys* Nth_app_l. }
        { lets [ (Heq0 & Heqty) | (m & Heqm & in_vs2) ] : Nth_cons_inv in_vs2'.
          { inverts* Heqty. simple_math. }
          { simple_math. constructor. apply* ok_env_strengthen_var. unfold var_in. rew_env.
            applys_eq* (>> Nth_app_r (vars G1 ++ [SkipVar]) in_vs2) ; rew_list~. nat_math. } } }
      { Case "TmLam". constructor. applys* ok_type_strengthen_var ty1.
        rewrite tm_open_subst_comm.
        applys_eq* (IHttype (tm_freshen t' 0) (BindVar ty0 :: G1)). rew_env*.
        rew_list. applys* tm_freshen_preservation. applys* ok_term_lc. }
      { Case "TmTyLam". constructor. applys* ok_kind_strengthen_var ty1.
        rewrite tm_ty_open_subst_comm.
        applys_eq* (IHttype (tm_ty_freshen t' 0) (BindTvar k :: G1)). rew_env*.
        rew_list. applys* tm_ty_freshen_preservation. applys* ok_term_lc. }
      { Case "TmTyApp". constructors*. applys* ok_type_strengthen_var ty1. }
    Qed.

    Lemma tm_ty_subst_preservation :
      forall Gamma t ty ty' k,
        ok_term (BindTvar k :: Gamma) (tm_ty_open t) (ty_open ty) ->
        ok_type Gamma ty' k ->
        ok_term Gamma (tm_ty_bsubst t 0 ty') (ty_bsubst ty 0 ty').
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
      { Case "TmApp". inverts ttype1. rewrite tm_subst_open.
        applys* ok_term_drop_var empty_env Gamma.
        applys* tm_subst_preservation empty_env Gamma ty1.
        applys* tm_freshen_preservation ttype2. }
      { Case "TmTyApp". inverts ttype. applys* tm_ty_subst_preservation. }
    Qed.
  End Soundness.
End Soundness.
