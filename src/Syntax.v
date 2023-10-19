From TLC Require Import LibList LibLogic LibMap LibSet LibNat.

Open Scope nat_scope.

Module Type PAT.
  Parameter pat : Type.
End PAT.

Module Syntax (P : PAT).
  Export P.
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

  (* Freshness *)
  (* A variable x is free in u if removing it and reintroducing it is a no-op. *)

  Definition tvar_fresh (x : tvar) (ty : type) : Prop :=
    ty_freshen (ty_defreshen ty x) x = ty.

  Definition var_fresh (x : var) (t : term) : Prop :=
    tm_freshen (tm_defreshen t x) x = t.

  Definition tm_tvar_fresh (x : tvar) (t : term) : Prop :=
    tm_ty_freshen (tm_ty_defreshen t x) x = t.

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

End Syntax.
