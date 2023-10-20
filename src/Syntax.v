From MCore Require Import Tactics.
From TLC Require Import LibString LibList LibLogic LibMap LibSet LibNat.

Open Scope nat_scope.

Module Type PAT.
  Parameter pat : Type.
End PAT.

Module Syntax (P : PAT).
  Export P.

  (************************)
  (** SYNTAX DEFINITIONS **)
  (************************)

  Definition tname : Set := nat.
  Definition tvar  : Set := nat.
  Definition var   : Set := nat.
  Definition con   : Set := nat.

  Definition data : Type := map tname (set con).

  Inductive kind : Type :=
  | KiType : kind
  (* | KiData : data -> kind *)
  .

  Inductive type : Type :=
  | TyBVar : tvar -> type
  | TyFVar : tvar -> type
  | TyArr  : type -> type -> type
  | TyAll  : kind -> type -> type
  (* | TyProd : type -> type -> type *)
  (* | TyCon  : type -> tname -> type *)
  (* | TySem  : type -> type -> list pat -> type *)
  (* | TyData : data -> type *)
  .

  #[export]
   Instance Inhab_type : Inhab type.
  Proof. apply (Inhab_of_val (TyFVar 0)). Qed.

  Inductive fin2 : Set := F1 | F2.

  Inductive term : Type :=
  | TmBVar   : var -> term
  | TmFVar   : var -> term
  | TmLam    : type -> term -> term
  | TmApp    : term -> term -> term
  | TmTyLam  : kind -> term -> term
  | TmTyApp  : term -> type -> term
  (* | TmFix    : term -> term *)
  (* | TmProd   : term -> term -> term *)
  (* | TmProj   : fin2 -> term -> term *)
  (* | TmCon    : con -> type -> term -> term *)
  (* | TmMatch  : term -> pat -> term -> term -> term *)
  (* | TmNever  : term *)
  (* | TmType   : term -> term *)
  (* | TmConDef : data -> type -> tname -> term -> term *)
  (* | TmSem    : type -> list (pat * term) -> term *)
  (* | TmComp   : term -> term -> term *)
  (* | TmSemApp : term -> term -> term *)
  .

  #[export]
   Instance Inhab_term : Inhab term.
  Proof. apply (Inhab_of_val (TmFVar 0)). Qed.


  (**************************)
  (** OPERATIONS ON SYNTAX **)
  (**************************)

  (* Freshening *)
  (* X_freshen u x represents an alpha-conversion making x fresh. *)

  Fixpoint ty_freshen (ty : type) (x : tvar) : type :=
    match ty with
    | TyBVar j => ty
    | TyFVar k => If x <= k then TyFVar (S k) else ty
    | TyArr l r => TyArr (ty_freshen l x) (ty_freshen r x)
    | TyAll k ty' => TyAll k (ty_freshen ty' x)
    (* | TyProd l r => TyProd (ty_shift_gen l x) (ty_shift_gen r x) *)
    (* | TyCon ty' T => TyCon (ty_shift_gen ty' x) T *)
    (* | TySem l r ps => TySem (ty_shift_gen l x) (ty_shift_gen r x) ps *)
    (* | TyData d => ty *)
    end.

  Fixpoint tm_freshen (t : term) (x : var) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => If x <= k then TmFVar (S k) else t
    | TmLam ty t' => TmLam ty (tm_freshen t' x)
    | TmApp l r => TmApp (tm_freshen l x) (tm_freshen r x)
    | TmTyLam k t' => TmTyLam k (tm_freshen t' x)
    | TmTyApp t' ty => TmTyApp (tm_freshen t' x) ty
    end.

  Fixpoint tm_ty_freshen (t : term) (x : tvar) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty t' => TmLam (ty_freshen ty x) (tm_ty_freshen t' x)
    | TmApp l r => TmApp (tm_ty_freshen l x) (tm_ty_freshen r x)
    | TmTyLam k t' => TmTyLam k (tm_ty_freshen t' x)
    | TmTyApp t' ty => TmTyApp (tm_ty_freshen t' x) (ty_freshen ty x)
    end.

  (* Defreshening *)
  (* X_defreshen u x represents an alpha-conversion making x occupied. *)

  Fixpoint ty_defreshen (ty : type) (x : tvar) : type :=
    match ty with
    | TyBVar j => ty
    | TyFVar k => If x < k then TyFVar (k - 1) else ty
    | TyArr l r => TyArr (ty_defreshen l x) (ty_defreshen r x)
    | TyAll k ty' => TyAll k (ty_defreshen ty' x)
    (* | TyProd l r => TyProd (ty_shift_gen l x) (ty_shift_gen r x) *)
    (* | TyCon ty' T => TyCon (ty_shift_gen ty' x) T *)
    (* | TySem l r ps => TySem (ty_shift_gen l x) (ty_shift_gen r x) ps *)
    (* | TyData d => ty *)
    end.

  Fixpoint tm_defreshen (t : term) (x : var) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => If x < k then TmFVar (k - 1) else t
    | TmLam ty t' => TmLam ty (tm_defreshen t' x)
    | TmApp l r => TmApp (tm_defreshen l x) (tm_defreshen r x)
    | TmTyLam k t' => TmTyLam k (tm_defreshen t' x)
    | TmTyApp t' ty => TmTyApp (tm_defreshen t' x) ty
    end.

  Fixpoint tm_ty_defreshen (t : term) (x : tvar) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty t' => TmLam (ty_defreshen ty x) (tm_ty_defreshen t' x)
    | TmApp l r => TmApp (tm_ty_defreshen l x) (tm_ty_defreshen r x)
    | TmTyLam k t' => TmTyLam k (tm_ty_defreshen t' x)
    | TmTyApp t' ty => TmTyApp (tm_ty_defreshen t' x) (ty_defreshen ty x)
    end.

  (* Freshness *)
  (* A variable x is free in u if removing it and reintroducing it is a no-op. *)

  Definition tvar_fresh (x : tvar) (ty : type) : Prop :=
    ty_freshen (ty_defreshen ty x) x = ty.

  Definition var_fresh (x : var) (t : term) : Prop :=
    tm_freshen (tm_defreshen t x) x = t.

  Definition tm_tvar_fresh (x : tvar) (t : term) : Prop :=
    tm_ty_freshen (tm_ty_defreshen t x) x = t.

  (* Bound variable substitution *)
  (* X_bsubst u x v represents the substitution u[x \mapsto v], where x is bound in u. *)

  Fixpoint ty_bsubst (ty1 : type) (x : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyBVar j => If x = j then ty2 else ty1
    | TyFVar k => ty1
    | TyArr l r =>
        TyArr (ty_bsubst l x ty2) (ty_bsubst r x ty2)
    | TyAll k ty1' =>
        TyAll k (ty_bsubst ty1' (S x) ty2)
    (* | TyProd l r => *)
    (*     TyProd (ty_fsubst_gen l x ty2) (ty_fsubst_gen r x ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_fsubst_gen ty1' x ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_fsubst_gen l x ty2) (ty_fsubst_gen r x ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Fixpoint tm_bsubst (t1 : term) (x : var) (t2 : term) : term :=
    match t1 with
    | TmBVar j => If x = j then t2 else t1
    | TmFVar k => t1
    | TmLam ty t1' => TmLam ty (tm_bsubst t1' (S x) t2)
    | TmApp l r => TmApp (tm_bsubst l x t2) (tm_bsubst r x t2)
    | TmTyLam k t1' => TmTyLam k (tm_bsubst t1' x t2)
    | TmTyApp t1' ty => TmTyApp (tm_bsubst t1' x t2) ty
    end.

  Fixpoint tm_ty_bsubst (t : term) (x : tvar) (ty : type) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty' t' => TmLam (ty_bsubst ty' x ty) (tm_ty_bsubst t' x ty)
    | TmApp l r => TmApp (tm_ty_bsubst l x ty) (tm_ty_bsubst r x ty)
    | TmTyLam k t' => TmTyLam k (tm_ty_bsubst t' (S x) ty)
    | TmTyApp t' ty' => TmTyApp (tm_ty_bsubst t' x ty) (ty_bsubst ty' x ty)
    end.

  (* Free variable substitution *)
  (* X_fsubst u x v represents the substitution u[x \mapsto v], where x is free in u. *)

  Fixpoint ty_fsubst (ty1 : type) (x : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyBVar j => ty1
    | TyFVar k => If x = k then ty2 else ty1
    | TyArr l r =>
        TyArr (ty_fsubst l x ty2) (ty_fsubst r x ty2)
    | TyAll k ty1' =>
        TyAll k (ty_fsubst ty1' x ty2)
    (* | TyProd l r => *)
    (*     TyProd (ty_fsubst_gen l x ty2) (ty_fsubst_gen r x ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_fsubst_gen ty1' x ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_fsubst_gen l x ty2) (ty_fsubst_gen r x ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Fixpoint tm_fsubst (t1 : term) (x : var) (t2 : term) : term :=
    match t1 with
    | TmBVar j => t1
    | TmFVar k => If x = k then t2 else t1
    | TmLam ty t1' => TmLam ty (tm_fsubst t1' x t2)
    | TmApp l r => TmApp (tm_fsubst l x t2) (tm_fsubst r x t2)
    | TmTyLam k t1' => TmTyLam k (tm_fsubst t1' x t2)
    | TmTyApp t1' ty => TmTyApp (tm_fsubst t1' x t2) ty
    end.

  Fixpoint tm_ty_fsubst (t : term) (x : tvar) (ty : type) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty' t' => TmLam (ty_fsubst ty' x ty) (tm_ty_fsubst t' x ty)
    | TmApp l r => TmApp (tm_ty_fsubst l x ty) (tm_ty_fsubst r x ty)
    | TmTyLam k t' => TmTyLam k (tm_ty_fsubst t' x ty)
    | TmTyApp t' ty' => TmTyApp (tm_ty_fsubst t' x ty) (ty_fsubst ty' x ty)
    end.

  (* Opening *)
  (* X_open u y x replaces the bound variable y in u with a fresh free variable x *)

  Definition ty_open (ty : type) (y : var) (x : var) : type :=
    ty_bsubst (ty_freshen ty x) y (TyFVar x).
  Definition tm_open (t : term) (y : var) (x : var) : term :=
    tm_bsubst (tm_freshen t x) y (TmFVar x).
  Definition tm_ty_open (t : term) (y : var) (x : var) : term :=
    tm_ty_bsubst (tm_ty_freshen t x) y (TyFVar x).

  (* Closing *)
  (* X_close u x v replaces the free variable x in u with the term v,
     performing alpha-conversion to ensure x is fresh in v *)

  Definition ty_close (ty : type) (x : tvar) (ty' : type) : type :=
    ty_defreshen (ty_fsubst ty x (ty_freshen ty' x)) x.
  Definition tm_close (t : term) (x : var) (t' : term) : term :=
    tm_defreshen (tm_fsubst t x (tm_freshen t' x)) x.
  Definition tm_ty_close (t : term) (x : tvar) (ty : type) : term :=
    tm_ty_defreshen (tm_ty_fsubst t x (ty_freshen ty x)) x.

  (* Definition tm_fsubst_n (t : term) (ts : list term) : term := *)
  (*   fold_right (fun t2 t1 => tm_fsubst t1 t2) t ts. *)

  (* Local closure *)
  (* A locally closed term contains no unbound BVars. *)

  Inductive ty_lc : type -> Prop :=
  | LCTFVar : forall v, ty_lc (TyFVar v)
  | LCTArr  : forall ty1 ty2, ty_lc ty1 -> ty_lc ty2 -> ty_lc (TyArr ty1 ty2)
  | LCTAll  : forall k ty, ty_lc (ty_open ty 0 0) -> ty_lc (TyAll k ty)
  .
  #[export]
   Hint Constructors ty_lc : mcore.

  Inductive tm_lc : term -> Prop :=
  | LCFVar  : forall v, tm_lc (TmFVar v)
  | LCLam   : forall t ty, ty_lc ty -> tm_lc (tm_open t 0 0) -> tm_lc (TmLam ty t)
  | LCApp   : forall t1 t2, tm_lc t1 -> tm_lc t2 -> tm_lc (TmApp t1 t2)
  | LCTyLam : forall k t, tm_lc (tm_ty_open t 0 0) -> tm_lc (TmTyLam k t)
  | LCTyApp : forall t ty, tm_lc t -> ty_lc ty -> tm_lc (TmTyApp t ty)
  .
  #[export]
   Hint Constructors tm_lc : mcore.


  (******************************)
  (** PROPERTIES OF OPERATIONS **)
  (******************************)

  Lemma tm_defreshen_freshen : forall t x, tm_defreshen (tm_freshen t x) x = t.
  Proof. magic t. Qed.

  Lemma ty_defreshen_freshen : forall t x, ty_defreshen (ty_freshen t x) x = t.
  Proof. magic t. Qed.

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
  Proof. magic ty. Qed.

  Lemma ty_freshen_defreshen :
    forall ty x y,
      x <= y ->
      ty_freshen (ty_defreshen ty y) x = ty_defreshen (ty_freshen ty x) (S y).
  Proof. magic ty. Qed.

  Lemma tm_ty_freshen_defreshen :
    forall ty x y,
      tm_ty_freshen (tm_defreshen ty y) x = tm_defreshen (tm_ty_freshen ty x) y.
  Proof. magic ty. Qed.


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


  Lemma tm_freshen_fsubst :
    forall t x y u,
      x <= y ->
      tm_freshen (tm_fsubst t y u) x =
        tm_fsubst (tm_freshen t x) (S y) (tm_freshen u x).
  Proof. magic t. Qed.

  Lemma ty_freshen_fsubst :
    forall t x y u,
      x <= y ->
      ty_freshen (ty_fsubst t y u) x =
        ty_fsubst (ty_freshen t x) (S y) (ty_freshen u x).
  Proof. magic t. Qed.

  Lemma tm_ty_freshen_fsubst :
    forall t x y u,
      tm_ty_freshen (tm_fsubst t y u) x =
        tm_fsubst (tm_ty_freshen t x) y (tm_ty_freshen u x).
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
      rewrite* tm_freshen_freshen.
      assert (Hfv : TmFVar 0 = tm_freshen (TmFVar 0) (S x)) by simple_math.
      rewrite Hfv. rewrite* <- tm_freshen_bsubst. }
    { Case "TmTyLam". constructor*. unfolds tm_ty_open.
      rewrite tm_ty_freshen_freshen. rewrite* <- tm_freshen_ty_bsubst. }
  Qed.

  #[export]
   Hint Extern 1 (tm_lc (tm_freshen ?t _)) =>
    match goal with
    | H: tm_lc t |- _ => apply tm_freshen_lc
    end
    : mcore.

  Lemma ty_freshen_lc : forall ty x, ty_lc ty -> ty_lc (ty_freshen ty x).
  Proof.
    introv Hlc. unfold ty_freshen.
    gen x.
    induction Hlc ; intros ; simpls*.
    { Case "TyFVar". case_if*. }
    { Case "TyAll". constructor*. unfolds ty_open.
      rewrite* ty_freshen_freshen.
      assert (Hfv : TyFVar 0 = ty_freshen (TyFVar 0) (S x)) by simple_math.
      rewrite Hfv. rewrite* <- ty_freshen_bsubst. }
  Qed.

  #[export]
   Hint Extern 1 (ty_lc (ty_freshen ?ty _)) =>
    match goal with
    | H: ty_lc ty |- _ => apply ty_freshen_lc
    end
    : mcore.

  Lemma tm_ty_freshen_lc : forall t x, tm_lc t -> tm_lc (tm_ty_freshen t x).
    introv Hlc.
    gen x.
    induction Hlc ; intros ; simpls*.
    { Case "TmLam". constructor*. unfolds tm_open.
      rewrite <- tm_ty_freshen_freshen.
      assert (Hfv : TmFVar 0 = tm_ty_freshen (TmFVar 0) x) by trivial.
      rewrite Hfv. rewrite* <- tm_ty_freshen_bsubst. }
    { Case "TmTyLam". constructor*. unfolds tm_ty_open.
      rewrite* tm_ty_freshen_ty_freshen.
      assert (Hfv : TyFVar 0 = ty_freshen (TyFVar 0) (S x)) by simple_math.
      rewrite Hfv. rewrite* <- tm_ty_freshen_ty_bsubst. }
  Qed.

  #[export]
   Hint Extern 1 (tm_lc (tm_ty_freshen ?t _)) =>
    match goal with
    | H: tm_lc t |- _ => apply tm_ty_freshen_lc
    end
    : mcore.

  Lemma ty_defreshen_lc : forall ty x, ty_lc ty -> ty_lc (ty_defreshen ty x).
  Proof.
    introv Hlc. unfold ty_defreshen.
    gen x.
    induction Hlc ; intros ; simpls*.
    { Case "TyFVar". case_if*. }
    { Case "TyAll". constructor*. unfolds ty_open.
      rewrite* ty_freshen_defreshen.
      assert (Hfv : TyFVar 0 = ty_defreshen (TyFVar 0) (S x)) by simple_math.
      rewrite Hfv. rewrite* <- ty_defreshen_bsubst. }
  Qed.


  Lemma tm_fsubst_fresh : forall t x u, var_fresh x t -> tm_fsubst t x u = t.
  Proof.
    introv Hfresh. unfolds.
    induction* t ; fequals ; try (injection Hfresh ; auto_star).
    { Case "TmFVar". cases_if*. lets* ? : var_not_fresh v. }
  Qed.

  Lemma ty_fsubst_fresh : forall t x u, tvar_fresh x t -> ty_fsubst t x u = t.
  Proof.
    introv Hfresh. unfolds.
    induction* t ; fequals ; try (injection Hfresh ; auto_star).
    { Case "TmFVar". cases_if*. lets* ? : tvar_not_fresh t. }
  Qed.

  (* TODO: These lemmas can be stated in terms of bsubst only, e.g., *)
  (*  x <> y ->
        ty_bsubst (ty_bsubst ty x ty1) y ty2 = ty_bsubst ty x ty1 ->
        ty_bsubst ty y ty2 = ty.
   *)
  (* Can we separate out the open/freshen part in a good way? *)
  Lemma ty_bsubst_neq : forall ty x y z ty',
      x <> y ->
      ty_bsubst (ty_open ty x z) y ty' = ty_open ty x z ->
      ty_bsubst ty y ty' = ty.
  Proof. unfolds ty_open ; magic ty ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

  Lemma tm_bsubst_neq : forall t x y z u,
      x <> y ->
      tm_bsubst (tm_open t x z) y u = tm_open t x z ->
      tm_bsubst t y u = t.
  Proof. unfolds tm_open ; magic t ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

  Lemma tm_ty_bsubst_neq : forall t x y z ty,
      x <> y ->
      tm_ty_bsubst (tm_ty_open t x z) y ty = tm_ty_open t x z ->
      tm_ty_bsubst t y ty = t.
  Proof.
    introv Hneq Heq ; gen x y ; magic t ; inverts* Heq ;
      with_hyp (ty_bsubst _ _ _ = _) as Heq1 ; applys ty_bsubst_neq Hneq Heq1.
  Qed.

  Lemma tm_bsubst_ty_rec : forall t x y z u,
      tm_bsubst (tm_ty_open t x z) y u = tm_ty_open t x z ->
      tm_bsubst t y u = t.
  Proof. magic t ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

  Lemma tm_ty_bsubst_rec : forall t x y z ty,
      tm_ty_bsubst (tm_open t x z) y ty = tm_open t x z ->
      tm_ty_bsubst t y ty = t.
  Proof. unfolds tm_open ; magic t ; with_hyp (_ = _) as Heq ; inverts* Heq. Qed.

  Lemma tm_bsubst_lc : forall t y u, tm_lc t -> tm_bsubst t y u = t.
  Proof.
    introv Hlc. gen y.
    induction Hlc ; intros ; simpls ; fequals*.
    { Case "TmLam". rewrite tm_bsubst_neq with (x := 0) (z := 0) ; auto. }
    { Case "TmTyLam". rewrite tm_bsubst_ty_rec with (x := 0) (z := 0) ; auto. }
  Qed.

  Lemma ty_bsubst_lc : forall ty y u, ty_lc ty -> ty_bsubst ty y u = ty.
  Proof.
    introv Hlc. gen y.
    induction Hlc ; intros ; simpls ; fequals*.
    { Case "TyAll". rewrite ty_bsubst_neq with (x := 0) (z := 0) ; auto. }
  Qed.

  Lemma tm_ty_bsubst_lc : forall t y ty, tm_lc t -> tm_ty_bsubst t y ty = t.
  Proof.
    introv Hlc. gen y.
    induction Hlc ; intros ; simpls ; fequals* ; try apply* ty_bsubst_lc.
    { Case "TmLam". rewrite tm_ty_bsubst_rec with (x := 0) (z := 0) ; auto. }
    { Case "TmTyLam". rewrite tm_ty_bsubst_neq with (x := 0) (z := 0) ; auto. }
  Qed.

  Lemma tm_fsubst_bsubst_distr :
    forall t x y u1 u2,
      tm_lc u1 ->
      tm_fsubst (tm_bsubst t y u2) x u1 =
        tm_bsubst (tm_fsubst t x u1) y (tm_fsubst u2 x u1).
  Proof. magic t ; rewrite* tm_bsubst_lc. Qed.

  Lemma ty_fsubst_bsubst_distr :
    forall t x y u1 u2,
      ty_lc u1 ->
      ty_fsubst (ty_bsubst t y u2) x u1 =
        ty_bsubst (ty_fsubst t x u1) y (ty_fsubst u2 x u1).
  Proof. magic t ; rewrite* ty_bsubst_lc. Qed.

  Lemma tm_fsubst_intro :
    forall t x y u,
      var_fresh x t ->
      tm_bsubst t y u = tm_fsubst (tm_bsubst t y (TmFVar x)) x u.
  Proof.
    introv Hfresh ; gen y ; magic t ; try (injection Hfresh ; auto_star).
    { Case "TmFVar". subst. lets* ? : var_not_fresh v. }
  Qed.

  Lemma ty_fsubst_intro :
    forall x y ty u,
      tvar_fresh x ty ->
      ty_bsubst ty y u = ty_fsubst (ty_bsubst ty y (TyFVar x)) x u.
  Proof.
    introv Hfresh ; gen y ; magic ty ; try (injection Hfresh ; auto_star).
    { Case "TmFVar". subst. lets* ? : tvar_not_fresh t. }
  Qed.

  Lemma tm_bsubst_close_open :
    forall t u x y,
      tm_bsubst t y u = tm_close (tm_open t y x) x u.
  Proof.
    intros.
    rewrite <- tm_defreshen_freshen with (x := x) (t := tm_bsubst t y u).
    rewrite tm_freshen_bsubst. rewrite tm_fsubst_intro with (x := x) ; auto. apply tm_freshen_fresh.
  Qed.

  Lemma ty_bsubst_close_open :
    forall ty u x y,
      ty_bsubst ty y u = ty_close (ty_open ty y x) x u.
  Proof.
    intros.
    rewrite <- ty_defreshen_freshen with (x := x) (t := ty_bsubst ty y u).
    rewrite ty_freshen_bsubst. rewrite ty_fsubst_intro with (x := x) ; auto. apply ty_freshen_fresh.
  Qed.

  Lemma tm_bsubst_fsubst_comm :
    forall t x y z u,
      x <> z ->
      tm_lc u ->
      tm_bsubst (tm_fsubst t x u) y (TmFVar z) =
        tm_fsubst (tm_bsubst t y (TmFVar z)) x u.
  Proof.
    introv Hneq Hlc. symmetry.
    applys_eq* tm_fsubst_bsubst_distr. fequals.
    rewrite* tm_fsubst_fresh. apply* var_neq_fresh.
  Qed.

  Lemma ty_bsubst_fsubst_comm :
    forall t x y z u,
      x <> z ->
      ty_lc u ->
      ty_bsubst (ty_fsubst t x u) y (TyFVar z) =
        ty_fsubst (ty_bsubst t y (TyFVar z)) x u.
  Proof.
    introv Hneq Hlc. symmetry.
    applys_eq* ty_fsubst_bsubst_distr. fequals.
    rewrite* ty_fsubst_fresh. apply* tvar_neq_fresh.
  Qed.

  Lemma tm_ty_bsubst_fsubst_comm :
    forall t x y u ty,
      tm_lc u ->
      tm_ty_bsubst (tm_fsubst t x u) y ty =
        tm_fsubst (tm_ty_bsubst t y ty) x u.
  Proof. magic t ; rewrite* tm_ty_bsubst_lc. Qed.

  Lemma tm_open_fsubst_comm :
    forall t x y z u,
      z <= x  ->
      tm_lc u ->
      tm_open (tm_fsubst t x u) y z = tm_fsubst (tm_open t y z) (S x) (tm_freshen u z).
  Proof.
    introv Hle Hlc. unfolds. rewrite* tm_freshen_fsubst. applys* tm_bsubst_fsubst_comm.
    nat_math.
  Qed.

  Lemma ty_open_fsubst_comm :
    forall t x y z u,
      z <= x  ->
      ty_lc u ->
      ty_open (ty_fsubst t x u) y z = ty_fsubst (ty_open t y z) (S x) (ty_freshen u z).
  Proof.
    introv Hle Hlc. unfolds. rewrite* ty_freshen_fsubst. applys* ty_bsubst_fsubst_comm.
    nat_math.
  Qed.

  Lemma tm_ty_open_fsubst_comm :
    forall t x y z u,
      tm_lc u ->
      tm_ty_open (tm_fsubst t x u) y z = tm_fsubst (tm_ty_open t y z) x (tm_ty_freshen u z).
  Proof.
    introv Hlc. unfolds. rewrite* tm_ty_freshen_fsubst. applys* tm_ty_bsubst_fsubst_comm.
  Qed.

  Lemma tm_open_defreshen_comm :
    forall t x y z,
      z <= x ->
      tm_open (tm_defreshen t x) y z = tm_defreshen (tm_open t y z) (S x).
  Proof.
    intros. unfolds. rewrite* tm_freshen_defreshen.
    assert (Hfv : TmFVar z = tm_defreshen (TmFVar z) (S x)) by simple_math.
    rewrite Hfv. rewrite <- tm_defreshen_bsubst. rewrite* <- Hfv.
  Qed.

  Lemma tm_ty_open_defreshen_comm :
    forall t x y z,
      tm_ty_open (tm_defreshen t x) y z = tm_defreshen (tm_ty_open t y z) x.
  Proof.
    intros. unfolds. rewrite tm_ty_freshen_defreshen.
    rewrite* tm_defreshen_ty_bsubst.
  Qed.

  Lemma tm_open_close_comm :
    forall t x y z u,
      z <= x  ->
      tm_lc u ->
      tm_open (tm_close t x u) y z =
        tm_close (tm_open t y z) (S x) (tm_freshen u z).
  Proof.
    introv Hle Hlc. unfold tm_close.
    rewrite* tm_open_defreshen_comm. rewrite* tm_open_fsubst_comm.
    rewrite* tm_freshen_freshen.
  Qed.

  Lemma tm_ty_open_close_comm :
    forall t x y z u,
      tm_lc u ->
      tm_ty_open (tm_close t x u) y z =
        tm_close (tm_ty_open t y z) x (tm_ty_freshen u z).
  Proof.
    intros. unfold tm_close.
    rewrite tm_ty_open_defreshen_comm. rewrite* tm_ty_open_fsubst_comm.
    rewrite* tm_ty_freshen_freshen.
  Qed.

  Lemma ty_lc_fsubst :
    forall ty1 ty2 x,
      ty_lc ty1 ->
      ty_lc ty2 ->
      ty_lc (ty_fsubst ty1 x ty2).
  Proof.
    introv Hlc1 Hlc2. gen x ty2.
    induction* Hlc1 ; intros ; simpls*.
    { Case "TyBVar". case_if*. }
    { Case "TyAll". constructor*. rewrite* ty_open_fsubst_comm. }
  Qed.

End Syntax.
