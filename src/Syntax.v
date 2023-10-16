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
  (* X_freshen u i represents an alpha-renaming making i fresh. *)

  Fixpoint ty_freshen (ty : type) (i : tvar) : type :=
    match ty with
    | TyBVar j => ty
    | TyFVar k => If i <= k then TyFVar (S k) else ty
    | TyArr l r => TyArr (ty_freshen l i) (ty_freshen r i)
    | TyAll k ty' => TyAll k (ty_freshen ty' i)
    (* | TyProd l r => TyProd (ty_shift_gen l i) (ty_shift_gen r i) *)
    (* | TyCon ty' T => TyCon (ty_shift_gen ty' i) T *)
    (* | TySem l r ps => TySem (ty_shift_gen l i) (ty_shift_gen r i) ps *)
    (* | TyData d => ty *)
    end.

  Fixpoint tm_freshen (t : term) (i : var) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => If i <= k then TmFVar (S k) else t
    | TmLam ty t' => TmLam ty (tm_freshen t' i)
    | TmApp l r => TmApp (tm_freshen l i) (tm_freshen r i)
    | TmTyLam k t' => TmTyLam k (tm_freshen t' i)
    | TmTyApp t' ty => TmTyApp (tm_freshen t' i) ty
    end.

  Fixpoint tm_ty_freshen (t : term) (i : tvar) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty t' => TmLam (ty_freshen ty i) (tm_ty_freshen t' i)
    | TmApp l r => TmApp (tm_ty_freshen l i) (tm_ty_freshen r i)
    | TmTyLam k t' => TmTyLam k (tm_ty_freshen t' i)
    | TmTyApp t' ty => TmTyApp (tm_ty_freshen t' i) (ty_freshen ty i)
    end.

  (* Defreshening *)
  (* X_defreshen u i represents an alpha-renaming making i occupied. *)

  Fixpoint ty_defreshen (ty : type) (i : tvar) : type :=
    match ty with
    | TyBVar j => ty
    | TyFVar k => If i <= k then TyFVar (k - 1) else ty
    | TyArr l r => TyArr (ty_defreshen l i) (ty_defreshen r i)
    | TyAll k ty' => TyAll k (ty_defreshen ty' i)
    (* | TyProd l r => TyProd (ty_shift_gen l i) (ty_shift_gen r i) *)
    (* | TyCon ty' T => TyCon (ty_shift_gen ty' i) T *)
    (* | TySem l r ps => TySem (ty_shift_gen l i) (ty_shift_gen r i) ps *)
    (* | TyData d => ty *)
    end.

  Fixpoint tm_defreshen (t : term) (i : var) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => If i <= k then TmFVar (k - 1) else t
    | TmLam ty t' => TmLam ty (tm_defreshen t' i)
    | TmApp l r => TmApp (tm_defreshen l i) (tm_defreshen r i)
    | TmTyLam k t' => TmTyLam k (tm_defreshen t' i)
    | TmTyApp t' ty => TmTyApp (tm_defreshen t' i) ty
    end.

  Fixpoint tm_ty_defreshen (t : term) (i : tvar) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty t' => TmLam (ty_defreshen ty i) (tm_ty_defreshen t' i)
    | TmApp l r => TmApp (tm_ty_defreshen l i) (tm_ty_defreshen r i)
    | TmTyLam k t' => TmTyLam k (tm_ty_defreshen t' i)
    | TmTyApp t' ty => TmTyApp (tm_ty_defreshen t' i) (ty_defreshen ty i)
    end.

  (* Bound variable substitution *)
  (* X_bsubst u i v represents the substitution u[i \mapsto v], where i is bound in u. *)

  Fixpoint ty_bsubst (ty1 : type) (i : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyBVar j => If j = i then ty2 else ty1
    | TyFVar k => ty1
    | TyArr l r =>
        TyArr (ty_bsubst l i ty2) (ty_bsubst r i ty2)
    | TyAll k ty1' =>
        TyAll k (ty_bsubst ty1' (S i) ty2)
    (* | TyProd l r => *)
    (*     TyProd (ty_subst_gen l i ty2) (ty_subst_gen r i ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_subst_gen ty1' i ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_subst_gen l i ty2) (ty_subst_gen r i ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Fixpoint tm_bsubst (t1 : term) (i : var) (t2 : term) : term :=
    match t1 with
    | TmBVar j => If j = i then t2 else t1
    | TmFVar k => t1
    | TmLam ty t1' => TmLam ty (tm_bsubst t1' (S i) t2)
    | TmApp l r => TmApp (tm_bsubst l i t2) (tm_bsubst r i t2)
    | TmTyLam k t1' => TmTyLam k (tm_bsubst t1' i t2)
    | TmTyApp t1' ty => TmTyApp (tm_bsubst t1' i t2) ty
    end.

  Fixpoint tm_ty_bsubst (t : term) (i : tvar) (ty : type) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty' t' => TmLam (ty_bsubst ty' i ty) (tm_ty_bsubst t' i ty)
    | TmApp l r => TmApp (tm_ty_bsubst l i ty) (tm_ty_bsubst r i ty)
    | TmTyLam k t' => TmTyLam k (tm_ty_bsubst t' (S i) ty)
    | TmTyApp t' ty' => TmTyApp (tm_ty_bsubst t' i ty) (ty_bsubst ty' i ty)
    end.

  (* Free variable substitution *)
  Fixpoint ty_subst (ty1 : type) (i : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyBVar j => ty1
    | TyFVar k => If k = i then ty2 else ty1
    | TyArr l r =>
        TyArr (ty_subst l i ty2) (ty_subst r i ty2)
    | TyAll k ty1' =>
        TyAll k (ty_subst ty1' i ty2)
    (* | TyProd l r => *)
    (*     TyProd (ty_subst_gen l i ty2) (ty_subst_gen r i ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_subst_gen ty1' i ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_subst_gen l i ty2) (ty_subst_gen r i ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Fixpoint tm_subst (t1 : term) (i : var) (t2 : term) : term :=
    match t1 with
    | TmBVar j => t1
    | TmFVar k => If k = i then t2 else t1
    | TmLam ty t1' => TmLam ty (tm_subst t1' i t2)
    | TmApp l r => TmApp (tm_subst l i t2) (tm_subst r i t2)
    | TmTyLam k t1' => TmTyLam k (tm_subst t1' i t2)
    | TmTyApp t1' ty => TmTyApp (tm_subst t1' i t2) ty
    end.

  Fixpoint tm_ty_subst (t : term) (i : tvar) (ty : type) : term :=
    match t with
    | TmBVar j => t
    | TmFVar k => t
    | TmLam ty' t' => TmLam (ty_subst ty' i ty) (tm_ty_subst t' i ty)
    | TmApp l r => TmApp (tm_ty_subst l i ty) (tm_ty_subst r i ty)
    | TmTyLam k t' => TmTyLam k (tm_ty_subst t' i ty)
    | TmTyApp t' ty' => TmTyApp (tm_ty_subst t' i ty) (ty_subst ty' i ty)
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

End Syntax.
