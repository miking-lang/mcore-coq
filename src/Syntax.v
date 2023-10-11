From TLC Require Import LibList LibLogic LibMap LibSet.

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
  | TyVar  : tvar -> type
  | TyArr  : type -> type -> type
  | TyAll  : kind -> type -> type
  (* | TyProd : type -> type -> type *)
  (* | TyCon  : type -> tname -> type *)
  (* | TySem  : type -> type -> list pat -> type *)
  (* | TyData : data -> type *)
  .

  Inductive fin2 : Set := F1 | F2.

  Inductive term : Type :=
  | TmVar    : var -> term
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
  Proof. apply (Inhab_of_val (TmVar 0)). Qed.

  (* Shifting and substitution *)
  (* X_shift_gen u i represents shifting all variables greater than or equal to i
     in the term u by one. *)
  (* X_subst_gen u i v represents the term u[i \mapsto v] *)

  Fixpoint ty_shift_gen (ty : type) (i : tvar) : type :=
    match ty with
    | TyVar j => (If i <= j then TyVar (S j) else ty)
    | TyArr l r => TyArr (ty_shift_gen l i) (ty_shift_gen r i)
    | TyAll k ty' => TyAll k (ty_shift_gen ty' (S i))
    (* | TyProd l r => TyProd (ty_shift_gen l i) (ty_shift_gen r i) *)
    (* | TyCon ty' T => TyCon (ty_shift_gen ty' i) T *)
    (* | TySem l r ps => TySem (ty_shift_gen l i) (ty_shift_gen r i) ps *)
    (* | TyData d => ty *)
    end.

  Definition ty_shift (ty : type) : type :=
    ty_shift_gen ty 0.

  Fixpoint ty_subst_gen (ty1 : type) (i : tvar) (ty2 : type) : type :=
    match ty1 with
    | TyVar j => (If i = j then ty2 else ty1)
    | TyArr l r =>
        TyArr (ty_subst_gen l i ty2) (ty_subst_gen r i ty2)
    | TyAll k ty1' =>
        TyAll k (ty_subst_gen ty1' (S i) (ty_shift ty2))
    (* | TyProd l r => *)
    (*     TyProd (ty_subst_gen l i ty2) (ty_subst_gen r i ty2) *)
    (* | TyCon ty1' T => *)
    (*     TyCon (ty_subst_gen ty1' i ty2) T *)
    (* | TySem l r ps => *)
    (*     TySem (ty_subst_gen l i ty2) (ty_subst_gen r i ty2) ps *)
    (* | TyData d => ty1 *)
    end.

  Definition ty_subst (ty1 : type) (ty2 : type) : type :=
    ty_subst_gen ty1 0 ty2.

  Fixpoint tm_shift_gen (t : term) (i : var) : term :=
    match t with
    | TmVar j => (If i <= j then TmVar (S j) else t)
    | TmLam ty t' => TmLam ty (tm_shift_gen t' (S i))
    | TmApp l r => TmApp (tm_shift_gen l i) (tm_shift_gen r i)
    | TmTyLam k t' => TmTyLam k (tm_shift_gen t' i)
    | TmTyApp t' ty => TmTyApp (tm_shift_gen t' i) ty
    end.

  Definition tm_shift (t : term) : term :=
    tm_shift_gen t 0.

  Fixpoint tm_subst_gen (t1 : term) (i : var) (t2 : term) : term :=
    match t1 with
    | TmVar j => (If i = j then t2 else t1)
    | TmLam ty t1' => TmLam ty (tm_subst_gen t1' (S i) (tm_shift t2))
    | TmApp l r => TmApp (tm_subst_gen l i t2) (tm_subst_gen r i t2)
    | TmTyLam k t1' => TmTyLam k (tm_subst_gen t1' i t2)
    | TmTyApp t1' ty => TmTyApp (tm_subst_gen t1' i t2) ty
    end.

  Definition tm_subst (t1 : term) (t2 : term) : term :=
    tm_subst_gen t1 0 t2.

  Definition tm_subst_n (t : term) (ts : list term) : term :=
    fold_right (fun t2 t1 => tm_subst t1 t2) t ts.

  Fixpoint tm_ty_subst_gen (t : term) (i : nat) (ty : type) : term :=
    match t with
    | TmVar j => t
    | TmLam ty' t' => TmLam (ty_subst_gen ty' i ty) (tm_ty_subst_gen t' i ty)
    | TmApp l r => TmApp (tm_ty_subst_gen l i ty) (tm_ty_subst_gen r i ty)
    | TmTyLam k t' => TmTyLam k (tm_ty_subst_gen t' (S i) ty)
    | TmTyApp t' ty' => TmTyApp (tm_ty_subst_gen t' i ty) (ty_subst_gen ty' i ty)
    end.

  Definition tm_ty_subst (t : term) (ty : type) : term :=
    tm_ty_subst_gen t 0 ty.

End Syntax.
