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
    Proof. magic t. Qed.

    Lemma ty_defreshen_freshen : forall t x, ty_defreshen (ty_freshen t x) x = t.
    Proof. magic t. Qed.

    Lemma tm_freshen_fresh : forall t x, var_fresh x (tm_freshen t x).
    Proof. intros ; unfolds ; rewrite* tm_defreshen_freshen. Qed.

    Lemma ty_freshen_fresh : forall t x, tvar_fresh x (ty_freshen t x).
    Proof. intros ; unfolds ; rewrite* ty_defreshen_freshen. Qed.

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

    Lemma tvar_neq_fresh : forall x y, x <> y -> tvar_fresh x (TyFVar y).
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

    Lemma ty_subst_fresh : forall t x u, tvar_fresh x t -> ty_subst t x u = t.
    Proof.
      introv Hfresh. unfolds.
      induction* t ; fequals ; try (injection Hfresh ; auto_star).
      { Case "TmFVar". cases_if*. lets* ? : tvar_not_fresh t. }
    Qed.

    Lemma tm_freshen_freshen :
      forall t x y,
        x <= y ->
        tm_freshen (tm_freshen t y) x = tm_freshen (tm_freshen t x) (S y).
    Proof. magic t. Qed.

    Lemma ty_freshen_freshen :
      forall ty x y,
        x <= y ->
        ty_freshen (ty_freshen ty y) x = ty_freshen (ty_freshen ty x) (S y).
    Proof. magic ty. Qed.

    Lemma tm_ty_freshen_ty_freshen :
      forall t x y,
        x <= y ->
        tm_ty_freshen (tm_ty_freshen t y) x = tm_ty_freshen (tm_ty_freshen t x) (S y).
    Proof. magic t ; applys* ty_freshen_freshen. Qed.

    Lemma tm_ty_freshen_freshen :
      forall t x y,
        tm_ty_freshen (tm_freshen t x) y = tm_freshen (tm_ty_freshen t y) x.
    Proof. magic t. Qed.

    Lemma tm_freshen_defreshen :
      forall ty x y,
        x <= y ->
        tm_freshen (tm_defreshen ty y) x = tm_defreshen (tm_freshen ty x) (S y).
    Proof. magic ty ; nat_math. Qed.

    Lemma ty_freshen_defreshen :
      forall ty x y,
        x <= y ->
        ty_freshen (ty_defreshen ty y) x = ty_defreshen (ty_freshen ty x) (S y).
    Proof. magic ty ; nat_math. Qed.

    Lemma tm_ty_freshen_defreshen :
      forall ty x y,
        tm_ty_freshen (tm_defreshen ty y) x = tm_defreshen (tm_ty_freshen ty x) y.
    Proof. magic ty. Qed.

    Lemma tm_freshen_subst :
      forall t x y u,
        x <= y ->
        tm_freshen (tm_subst t y u) x =
          tm_subst (tm_freshen t x) (S y) (tm_freshen u x).
    Proof. magic t. Qed.

    Lemma ty_freshen_subst :
      forall t x y u,
        x <= y ->
        ty_freshen (ty_subst t y u) x =
          ty_subst (ty_freshen t x) (S y) (ty_freshen u x).
    Proof. magic t. Qed.

    Lemma tm_ty_freshen_subst :
      forall t x y u,
        tm_ty_freshen (tm_subst t y u) x =
          tm_subst (tm_ty_freshen t x) y (tm_ty_freshen u x).
    Proof. magic t. Qed.

    Lemma tm_freshen_bsubst : forall t y z u,
        tm_freshen (tm_bsubst t y u) z =
          tm_bsubst (tm_freshen t z) y (tm_freshen u z).
    Proof. magic t. Qed.

    Lemma ty_freshen_bsubst : forall t y z u,
        ty_freshen (ty_bsubst t y u) z =
          ty_bsubst (ty_freshen t z) y (ty_freshen u z).
    Proof. magic t. Qed.

    Lemma tm_freshen_ty_bsubst : forall t y z u,
        tm_freshen (tm_ty_bsubst t y u) z =
          tm_ty_bsubst (tm_freshen t z) y u.
    Proof. magic t. Qed.

    Lemma tm_ty_freshen_bsubst : forall t y z u,
        tm_ty_freshen (tm_bsubst t y u) z =
          tm_bsubst (tm_ty_freshen t z) y (tm_ty_freshen u z).
    Proof. magic t. Qed.

    Lemma tm_ty_freshen_ty_bsubst : forall t y z u,
        tm_ty_freshen (tm_ty_bsubst t y u) z =
          tm_ty_bsubst (tm_ty_freshen t z) y (ty_freshen u z).
    Proof. magic t ; apply* ty_freshen_bsubst. Qed.

    Lemma tm_defreshen_bsubst : forall t y z u,
        tm_defreshen (tm_bsubst t y u) z =
          tm_bsubst (tm_defreshen t z) y (tm_defreshen u z).
    Proof. magic t. Qed.

    Lemma ty_defreshen_bsubst : forall t y z u,
        ty_defreshen (ty_bsubst t y u) z =
          ty_bsubst (ty_defreshen t z) y (ty_defreshen u z).
    Proof. magic t. Qed.

    Lemma tm_defreshen_ty_bsubst : forall t y z u,
        tm_defreshen (tm_ty_bsubst t y u) z =
          tm_ty_bsubst (tm_defreshen t z) y u.
    Proof. magic t. Qed.

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
        rewrite tm_ty_freshen_freshen. rewrite* <- tm_freshen_ty_bsubst. }
    Qed.

    Lemma ty_freshen_lc : forall ty x, ty_lc ty -> ty_lc (ty_freshen ty x).
    Proof.
      introv Hlc. unfold ty_freshen.
      gen x.
      induction Hlc ; intros ; simpls*.
      { Case "TyFVar". case_if*. }
      { Case "TyAll". constructor*. unfolds ty_open.
        rewrite ty_freshen_freshen ; try nat_math.
        assert (Hfv : TyFVar 0 = ty_freshen (TyFVar 0) (S x)) by simple_math.
        rewrite Hfv. rewrite* <- ty_freshen_bsubst. }
    Qed.

    Lemma tm_ty_freshen_lc : forall t x, tm_lc t -> tm_lc (tm_ty_freshen t x).
      introv Hlc.
      gen x.
      induction Hlc ; intros ; simpls*.
      { Case "TmLam". constructor*. apply* ty_freshen_lc. unfolds tm_open.
        rewrite <- tm_ty_freshen_freshen.
        assert (Hfv : TmFVar 0 = tm_ty_freshen (TmFVar 0) x) by trivial.
        rewrite Hfv. rewrite* <- tm_ty_freshen_bsubst. }
      { Case "TmTyLam". constructor*. unfolds tm_ty_open.
        rewrite tm_ty_freshen_ty_freshen ; try nat_math.
        assert (Hfv : TyFVar 0 = ty_freshen (TyFVar 0) (S x)) by simple_math.
        rewrite Hfv. rewrite* <- tm_ty_freshen_ty_bsubst. }
      { Case "TmTyApp". constructor*. apply* ty_freshen_lc. }
    Qed.

    Lemma ty_defreshen_lc : forall ty x, ty_lc ty -> ty_lc (ty_defreshen ty x).
    Proof.
      introv Hlc. unfold ty_defreshen.
      gen x.
      induction Hlc ; intros ; simpls*.
      { Case "TyFVar". case_if*. }
      { Case "TyAll". constructor*. unfolds ty_open.
        rewrite ty_freshen_defreshen ; try nat_math.
        assert (Hfv : TyFVar 0 = ty_defreshen (TyFVar 0) (S x)) by simple_math.
        rewrite Hfv. rewrite* <- ty_defreshen_bsubst. }
    Qed.

    (* TODO: can freshen be separated out from these lemmas into separate ones? *)
    Lemma ty_bsubst_neq : forall ty x y ty1 ty2,
        x <> y ->
        ty_bsubst (ty_bsubst (ty_freshen ty 0) x ty1) y ty2 = ty_bsubst (ty_freshen ty 0) x ty1 ->
        ty_bsubst ty y ty2 = ty.
    Proof. magic ty ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

    Lemma tm_bsubst_neq : forall t x y u1 u2,
        x <> y ->
        tm_bsubst (tm_bsubst (tm_freshen t 0) x u1) y u2 = tm_bsubst (tm_freshen t 0) x u1 ->
        tm_bsubst t y u2 = t.
    Proof. magic t ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

    Lemma tm_ty_bsubst_neq : forall t x y ty1 ty2,
        x <> y ->
        tm_ty_bsubst (tm_ty_bsubst (tm_ty_freshen t 0) x ty1) y ty2 =
          tm_ty_bsubst (tm_ty_freshen t 0) x ty1 ->
        tm_ty_bsubst t y ty2 = t.
    Proof.
      introv Hneq Heq ; gen x y ; magic t ; inverts* Heq ;
        with_hyp (ty_bsubst _ _ _ = _) as Heq1 ; applys ty_bsubst_neq Hneq Heq1.
    Qed.

    Lemma tm_bsubst_ty_rec : forall t x y ty u,
        tm_bsubst (tm_ty_bsubst (tm_ty_freshen t 0) x ty) y u =
          tm_ty_bsubst (tm_ty_freshen t 0) x ty ->
        tm_bsubst t y u = t.
    Proof. magic t ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

    Lemma tm_ty_bsubst_rec : forall t x y ty u,
        tm_ty_bsubst (tm_bsubst (tm_freshen t 0) x u) y ty =
          tm_bsubst (tm_freshen t 0) x u ->
        tm_ty_bsubst t y ty = t.
    Proof. magic t ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

    Lemma tm_bsubst_lc : forall t y u, tm_lc t -> tm_bsubst t y u = t.
    Proof.
      introv Hlc. gen y.
      induction Hlc ; intros ; simpls ; fequals*.
      { Case "TmLam". rewrite tm_bsubst_neq with (x := 0) (u1 := TmFVar 0) ; auto. }
      { Case "TmTyLam". rewrite tm_bsubst_ty_rec with (x := 0) (ty := TyFVar 0) ; auto. }
    Qed.

    Lemma ty_bsubst_lc : forall ty y u, ty_lc ty -> ty_bsubst ty y u = ty.
    Proof.
      introv Hlc. gen y.
      induction Hlc ; intros ; simpls ; fequals*.
      { Case "TyAll". rewrite ty_bsubst_neq with (x := 0) (ty1 := TyFVar 0) ; auto. }
    Qed.

    Lemma tm_ty_bsubst_lc : forall t y ty, tm_lc t -> tm_ty_bsubst t y ty = t.
    Proof.
      introv Hlc. gen y.
      induction Hlc ; intros ; simpls ; fequals* ; try apply* ty_bsubst_lc.
      { Case "TmLam". rewrite tm_ty_bsubst_rec with (x := 0) (u := TmFVar 0) ; auto. }
      { Case "TmTyLam". rewrite tm_ty_bsubst_neq with (x := 0) (ty1 := TyFVar 0) ; auto. }
    Qed.

    Lemma tm_subst_bsubst_distr :
      forall t x y u1 u2,
        tm_lc u1 ->
        tm_subst (tm_bsubst t y u2) x u1 =
          tm_bsubst (tm_subst t x u1) y (tm_subst u2 x u1).
    Proof. magic t ; rewrite* tm_bsubst_lc. Qed.

    Lemma ty_subst_bsubst_distr :
      forall t x y u1 u2,
        ty_lc u1 ->
        ty_subst (ty_bsubst t y u2) x u1 =
          ty_bsubst (ty_subst t x u1) y (ty_subst u2 x u1).
    Proof. magic t ; rewrite* ty_bsubst_lc. Qed.

    Lemma tm_subst_intro :
      forall t x y u,
        var_fresh x t ->
        tm_bsubst t y u = tm_subst (tm_bsubst t y (TmFVar x)) x u.
    Proof.
      introv Hfresh ; gen y ; magic t ; try (injection Hfresh ; auto_star).
      { Case "TmFVar". subst. lets* ? : var_not_fresh v. }
    Qed.

    Lemma ty_subst_intro :
      forall x y ty u,
        tvar_fresh x ty ->
        ty_bsubst ty y u = ty_subst (ty_bsubst ty y (TyFVar x)) x u.
    Proof.
      introv Hfresh ; gen y ; magic ty ; try (injection Hfresh ; auto_star).
      { Case "TmFVar". subst. lets* ? : tvar_not_fresh t. }
    Qed.

    Lemma tm_subst_open :
      forall t u,
        tm_bsubst t 0 u = tm_defreshen (tm_subst (tm_open t) 0 (tm_freshen u 0)) 0.
    Proof.
      intros.
      rewrite <- tm_defreshen_freshen with (x := 0) (t := tm_bsubst t 0 u).
      rewrite tm_freshen_bsubst. rewrite tm_subst_intro with (x := 0) ; auto. apply tm_freshen_fresh.
    Qed.

    Lemma ty_subst_open :
      forall ty u,
        ty_bsubst ty 0 u = ty_defreshen (ty_subst (ty_open ty) 0 (ty_freshen u 0)) 0.
    Proof.
      intros.
      rewrite <- ty_defreshen_freshen with (x := 0) (t := ty_bsubst ty 0 u).
      rewrite ty_freshen_bsubst. rewrite ty_subst_intro with (x := 0) ; auto. apply ty_freshen_fresh.
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

    Lemma ty_bsubst_subst_comm :
      forall t x y z u,
        x <> z ->
        ty_lc u ->
        ty_bsubst (ty_subst t x u) y (TyFVar z) =
          ty_subst (ty_bsubst t y (TyFVar z)) x u.
    Proof.
      introv Hneq Hlc. symmetry.
      applys_eq* ty_subst_bsubst_distr. fequals.
      rewrite* ty_subst_fresh. apply* tvar_neq_fresh.
    Qed.

    Lemma tm_ty_bsubst_subst_comm :
      forall t x y u ty,
        tm_lc u ->
        tm_ty_bsubst (tm_subst t x u) y ty =
          tm_subst (tm_ty_bsubst t y ty) x u.
    Proof. magic t ; rewrite* tm_ty_bsubst_lc. Qed.

    Lemma tm_open_subst_comm :
      forall t x u,
        tm_lc u ->
        tm_open (tm_subst t x u) = tm_subst (tm_open t) (S x) (tm_freshen u 0).
    Proof.
      introv Hlc. unfolds. rewrite tm_freshen_subst. applys* tm_bsubst_subst_comm.
      apply* tm_freshen_lc. nat_math.
    Qed.

    Lemma ty_open_subst_comm :
      forall t x u,
        ty_lc u ->
        ty_open (ty_subst t x u) = ty_subst (ty_open t) (S x) (ty_freshen u 0).
    Proof.
      introv Hlc. unfolds. rewrite ty_freshen_subst. applys* ty_bsubst_subst_comm.
      apply* ty_freshen_lc. nat_math.
    Qed.

    Lemma tm_ty_open_subst_comm :
      forall t x u,
        tm_lc u ->
        tm_ty_open (tm_subst t x u) = tm_subst (tm_ty_open t) x (tm_ty_freshen u 0).
    Proof.
      introv Hlc. unfolds. rewrite tm_ty_freshen_subst. applys* tm_ty_bsubst_subst_comm.
      apply* tm_ty_freshen_lc.
    Qed.

    Lemma tm_open_defreshen_comm :
      forall t x,
        tm_open (tm_defreshen t x) = tm_defreshen (tm_open t) (S x).
    Proof.
      intros. unfolds. rewrite tm_freshen_defreshen ; try nat_math.
      assert (Hfv : TmFVar 0 = tm_defreshen (TmFVar 0) (S x)) by simple_math.
      rewrite Hfv. rewrite <- tm_defreshen_bsubst. rewrite* <- Hfv.
    Qed.

    Lemma tm_ty_open_defreshen_comm :
      forall t x,
        tm_ty_open (tm_defreshen t x) = tm_defreshen (tm_ty_open t) x.
    Proof.
      intros. unfolds. rewrite tm_ty_freshen_defreshen.
      rewrite* tm_defreshen_ty_bsubst.
    Qed.

    Lemma ty_lc_subst :
      forall ty1 ty2 x,
        ty_lc ty1 ->
        ty_lc ty2 ->
        ty_lc (ty_subst ty1 x ty2).
    Proof.
      introv Hlc1 Hlc2. gen x ty2.
      induction* Hlc1 ; intros ; simpls*.
      { Case "TyBVar". case_if*. }
      { Case "TyAll". constructor*. rewrite* ty_open_subst_comm.
        applys* IHHlc1. apply* ty_freshen_lc. }
    Qed.

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
      { Case "TmFVar". with_hyp (var_in _ _ _) as Hvar. rew_env in Hvar. unfolds var_in.
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
        with_hyp (var_in _ _ _) as Hvar. rew_env in Hvar. unfolds var_in.
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
