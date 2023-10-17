From TLC Require Import LibList LibLogic LibMap LibSet LibNat.

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
  (* X_freshen u x represents an alpha-renaming making x fresh. *)

  Fixpoint ty_freshen (ty : type) (x : tvar) : type :=
    match ty with
    | TyBVar j => ty
    | TyFVar k => If k >= x then TyFVar (S k) else ty
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
    | TmFVar k => If k >= x then TmFVar (S k) else t
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
  (* X_defreshen u i represents an alpha-renaming making i occupied. *)

  Fixpoint ty_defreshen (ty : type) (x : tvar) : type :=
    match ty with
    | TyBVar j => ty
    | TyFVar k => If k > x then TyFVar (k - 1) else ty
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
    | TmFVar k => If k > x then TmFVar (k - 1) else t
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
  (* X_bsubst u i v represents the substitution u[i \mapsto v], where i is bound in u. *)

  Fixpoint ty_bsubst (ty1 : type) (x : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyBVar j => If j = x then ty2 else ty1
    | TyFVar k => ty1
    | TyArr l r =>
        TyArr (ty_bsubst l x ty2) (ty_bsubst r x ty2)
    | TyAll k ty1' =>
        TyAll k (ty_bsubst ty1' (S x) ty2)
    (* | TyProd l r => *)
    (*     TyProd (ty_subst_gen l x ty2) (ty_subst_gen r x ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_subst_gen ty1' x ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_subst_gen l x ty2) (ty_subst_gen r x ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Fixpoint tm_bsubst (t1 : term) (x : var) (t2 : term) : term :=
    match t1 with
    | TmBVar j => If j = x then t2 else t1
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
  Fixpoint ty_subst (ty1 : type) (x : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyBVar j => ty1
    | TyFVar k => If k = x then ty2 else ty1
    | TyArr l r =>
        TyArr (ty_subst l x ty2) (ty_subst r x ty2)
    | TyAll k ty1' =>
        TyAll k (ty_subst ty1' x ty2)
    (* | TyProd l r => *)
    (*     TyProd (ty_subst_gen l x ty2) (ty_subst_gen r x ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_subst_gen ty1' x ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_subst_gen l x ty2) (ty_subst_gen r x ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Fixpoint tm_subst (t1 : term) (x : var) (t2 : term) : term :=
    match t1 with
    | TmBVar j => t1
    | TmFVar k => If k = x then t2 else t1
    | TmLam ty t1' => TmLam ty (tm_subst t1' x t2)
    | TmApp l r => TmApp (tm_subst l x t2) (tm_subst r x t2)
    | TmTyLam k t1' => TmTyLam k (tm_subst t1' x t2)
    | TmTyApp t1' ty => TmTyApp (tm_subst t1' x t2) ty
    end.

  Fixpoint tm_ty_subst (t : term) (x : tvar) (ty : type) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty' t' => TmLam (ty_subst ty' x ty) (tm_ty_subst t' x ty)
    | TmApp l r => TmApp (tm_ty_subst l x ty) (tm_ty_subst r x ty)
    | TmTyLam k t' => TmTyLam k (tm_ty_subst t' x ty)
    | TmTyApp t' ty' => TmTyApp (tm_ty_subst t' x ty) (ty_subst ty' x ty)
    end.

  (* Opening *)
  Definition ty_open (ty : type) : type := ty_bsubst (ty_freshen ty 0) 0 (TyFVar 0).
  Definition tm_open (t : term) : term := tm_bsubst (tm_freshen t 0) 0 (TmFVar 0).
  Definition tm_ty_open (t : term) : term := tm_ty_bsubst (tm_ty_freshen t 0) 0 (TyFVar 0).

  (* Closing *)
  Definition ty_close (ty : type) : type := ty_defreshen (ty_subst ty 0 (TyBVar 0)) 0.
  Definition tm_close (t : term) : term := tm_defreshen (tm_subst t 0 (TmBVar 0)) 0.
  Definition tm_ty_close (t : term) : term := tm_ty_defreshen (tm_ty_subst t 0 (TyBVar 0)) 0.

  (* Definition tm_subst_n (t : term) (ts : list term) : term := *)
  (*   fold_right (fun t2 t1 => tm_subst t1 t2) t ts. *)

  Definition tm_tvar_fresh (x : var) (t : term) : Prop :=
    tm_ty_freshen (tm_ty_defreshen t x) x = t.

  Definition var_fresh (x : var) (t : term) : Prop :=
    tm_freshen (tm_defreshen t x) x = t.

  Inductive ty_lc : type -> Prop :=
  | LCTFVar : forall v, ty_lc (TyFVar v)
  | LCTArr  : forall ty1 ty2, ty_lc ty1 -> ty_lc ty2 -> ty_lc (TyArr ty1 ty2)
  | LCTAll  : forall k ty, ty_lc (ty_open ty) -> ty_lc (TyAll k ty)
  .
  #[export]
   Hint Constructors ty_lc : mcore.

  Inductive tm_lc : term -> Prop :=
  | LCFVar  : forall v, tm_lc (TmFVar v)
  | LCLam   : forall t ty, ty_lc ty -> tm_lc (tm_open t) -> tm_lc (TmLam ty t)
  | LCApp   : forall t1 t2, tm_lc t1 -> tm_lc t2 -> tm_lc (TmApp t1 t2)
  | LCTyLam : forall k t, tm_lc (tm_ty_open t) -> tm_lc (TmTyLam k t)
  | LCTyApp : forall t ty, tm_lc t -> ty_lc ty -> tm_lc (TmTyApp t ty)
  .
  #[export]
   Hint Constructors tm_lc : mcore.

End Syntax.
