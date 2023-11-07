From TLC Require Import LibList LibMonoid LibLN.

(************************)
(** SYNTAX DEFINITIONS **)
(************************)


(* We define constructor names and operations on them up front to
   avoid a mutual dependency between the syntax module and the
   abstract type of patterns *)

Definition bvar  : Set := nat.

Inductive con : Set :=
| BCon : bvar -> con
| FCon : var  -> con.

Notation Kfv K :=
  match K with
  | BCon X => \{}
  | FCon X => \{X}
  end.

Definition Kopen (j : nat) (X : con) (K : con) :=
  match K with
  | BCon i => (If i = j then X else K)
  | FCon _ => K
  end.

Definition Kclose (X : var) (j : nat) (K : con) :=
  match K with
  | BCon _ => K
  | FCon Y => If X = Y then BCon j else K
end.

Notation lcK K := (exists K', K = FCon K').

Definition Ksubst (X : var) (U : con) (K : con) :=
  match K with
  | BCon _ => K
  | FCon Y => (If X = Y then U else K)
  end.

Definition varsM : monoid_op vars :=
  {| monoid_oper := fun A B => A \u B ; monoid_neutral := \{} |}.

Lemma Monoid_varsM : Monoid varsM.
Proof.
  split.
  - apply~ union_assoc.
  - apply~ union_empty_l.
  - apply~ union_empty_r.
Qed.
#[export]
Hint Resolve Monoid_varsM : mcore.

Module Type PAT.
  Parameter pat : Type.

  Parameter pat_inhab : Inhab pat.

  Parameter Kfv_p : pat -> vars.
  Parameter Kopen_p : nat -> con -> pat -> pat.
  Parameter Kclose_p : var -> nat -> pat -> pat.
  Parameter lcp : pat -> Prop.
  Parameter Ksubst_p : var -> con -> pat -> pat.
End PAT.

Module Syntax (P : PAT).
  Export P.

  #[export]
   Instance Inhab_pat : Inhab pat.
  Proof. apply pat_inhab. Qed.

  Inductive tname : Set :=
  | BTName : bvar -> tname
  | FTName : var  -> tname.

  Definition data : Type :=
    list (tname * list con).

  Inductive kind : Type :=
  | KiType : kind
  | KiData : data -> kind.

  Inductive type : Type :=
  | TyBVar : bvar -> type
  | TyFVar : var  -> type
  | TyArr  : type -> type -> type
  | TyAll  : kind -> type -> type
  | TyProd : type -> type -> type
  | TyCon  : type -> tname -> type
  | TySem  : type -> type -> list pat -> type
  | TyData : data -> type.

  #[export]
   Instance Inhab_type : Inhab type.
  Proof. apply (Inhab_of_val (TyBVar 0)). Qed.

  Inductive fin2 : Set := F1 | F2.

  Inductive term : Type :=
  | TmBVar   : bvar -> term
  | TmFVar   : var  -> term
  | TmLam    : type -> term -> term
  | TmApp    : term -> term -> term
  | TmTyLam  : kind -> term -> term
  | TmTyApp  : term -> type -> term
  | TmFix    : term -> term
  | TmProd   : term -> term -> term
  | TmProj   : fin2 -> term -> term
  | TmCon    : con -> type -> term -> term
  | TmMatch  : term -> pat -> term -> term -> term
  | TmNever  : type -> term
  | TmType   : term -> term
  | TmConDef : data -> type -> tname -> term -> term
  | TmSem    : type -> pat  -> term -> term
  | TmComp   : term -> term -> term
  | TmSemApp : term -> term -> term.

  #[export]
   Instance Inhab_term : Inhab term.
  Proof. apply (Inhab_of_val (TmBVar 0)). Qed.


  (**************************)
  (** OPERATIONS ON SYNTAX **)
  (**************************)

  (* Notation scheme:
     - curly braces indicate type-level operations, and square braces indicate term-level ones
     - curly arrows indicate operations on bound variables, and double ones indicate free variables
     - type-level operation names generally start with t
     - type-level operations working over terms are suffixed by _t
   *)


  (* Free variables *)

  Fixpoint tfv (T : type) :=
    match T with
    | TyBVar X => \{}
    | TyFVar X => \{X}
    | TyArr T1 T2 => tfv T1 \u tfv T2
    | TyAll k T' => tfv T'
    | TyProd T1 T2 => tfv T1 \u tfv T2
    | TyCon ty T => tfv ty
    | TySem T1 T2 ps => tfv T1 \u tfv T2
    | TyData d => \{}
    end.

  Fixpoint tfv_t (t : term) :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{}
    | TmLam T t' => tfv T \u tfv_t t'
    | TmApp t1 t2 => tfv_t t1 \u tfv_t t2
    | TmTyLam k t' => tfv_t t'
    | TmTyApp t' T => tfv_t t' \u tfv T
    | TmFix t' => tfv_t t'
    | TmProd t1 t2 => tfv_t t1 \u tfv_t t2
    | TmProj i t' => tfv_t t'
    | TmCon K ty t' => tfv ty \u tfv_t t'
    | TmMatch t1 p t2 t3 => tfv_t t1 \u tfv_t t2 \u tfv_t t3
    | TmNever ty => tfv ty
    | TmType t' => tfv_t t'
    | TmConDef d ty T t' => tfv ty \u tfv_t t'
    | TmSem ty p t' => tfv ty \u tfv_t t'
    | TmComp t1 t2 => tfv_t t1 \u tfv_t t2
    | TmSemApp t1 t2 => tfv_t t1 \u tfv_t t2
    end.

  Fixpoint fv (t : term) :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{x}
    | TmLam T t' => fv t'
    | TmApp t1 t2 => fv t1 \u fv t2
    | TmTyLam k t' => fv t'
    | TmTyApp t' T => fv t'
    | TmFix t' => fv t'
    | TmProd t1 t2 => fv t1 \u fv t2
    | TmProj i t' => fv t'
    | TmCon K ty t' => fv t'
    | TmMatch t1 p t2 t3 => fv t1 \u fv t2 \u fv t3
    | TmNever ty => \{}
    | TmType t' => fv t'
    | TmConDef d ty T t' => fv t'
    | TmSem ty p t' => fv t'
    | TmComp t1 t2 => fv t1 \u fv t2
    | TmSemApp t1 t2 => fv t1 \u fv t2
    end.

  Notation Tfv T :=
    match T with
    | BTName X => \{}
    | FTName X => \{X}
    end.

  Definition Tfv_d (d : data) : vars :=
    fold varsM (fun '(T, Ks) => Tfv T) d.

  Definition Tfv_k (k : kind) : vars :=
    match k with
    | KiType => \{}
    | KiData d => Tfv_d d
    end.

  Fixpoint Tfv_ty (T : type) : vars :=
    match T with
    | TyBVar X => \{}
    | TyFVar X => \{}
    | TyArr T1 T2 => Tfv_ty T1 \u Tfv_ty T2
    | TyAll k T' => Tfv_k k \u Tfv_ty T'
    | TyProd T1 T2 => Tfv_ty T1 \u Tfv_ty T2
    | TyCon ty T => Tfv_ty ty \u Tfv T
    | TySem T1 T2 ps => Tfv_ty T1 \u Tfv_ty T2
    | TyData d => Tfv_d d
    end.

  Fixpoint Tfv_t (t : term) : vars :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{}
    | TmLam T t' => Tfv_ty T \u Tfv_t t'
    | TmApp t1 t2 => Tfv_t t1 \u Tfv_t t2
    | TmTyLam k t' => Tfv_k k \u Tfv_t t'
    | TmTyApp t' T => Tfv_t t' \u Tfv_ty T
    | TmFix t' => Tfv_t t'
    | TmProd t1 t2 => Tfv_t t1 \u Tfv_t t2
    | TmProj i t' => Tfv_t t'
    | TmCon K ty t' => Tfv_ty ty \u Tfv_t t'
    | TmMatch t1 p t2 t3 => Tfv_t t1 \u Tfv_t t2 \u Tfv_t t3
    | TmNever ty => Tfv_ty ty
    | TmType t' => Tfv_t t'
    | TmConDef d ty T t' => Tfv_d d \u Tfv_ty ty \u Tfv T \u Tfv_t t'
    | TmSem ty p t' => Tfv_ty ty \u Tfv_t t'
    | TmComp t1 t2 => Tfv_t t1 \u Tfv_t t2
    | TmSemApp t1 t2 => Tfv_t t1 \u Tfv_t t2
    end.

  Definition Kfv_d (d : data) : vars :=
    fold varsM (fun '(T, Ks) => fold varsM (fun K => Kfv K) Ks) d.

  Definition Kfv_k (k : kind) : vars :=
    match k with
    | KiType => \{}
    | KiData d => Kfv_d d
    end.

  Fixpoint Kfv_ty (T : type) : vars :=
    match T with
    | TyBVar X => \{}
    | TyFVar X => \{}
    | TyArr T1 T2 => Kfv_ty T1 \u Kfv_ty T2
    | TyAll k T' => Kfv_k k \u Kfv_ty T'
    | TyProd T1 T2 => Kfv_ty T1 \u Kfv_ty T2
    | TyCon ty T => Kfv_ty ty
    | TySem T1 T2 ps => Kfv_ty T1 \u Kfv_ty T2 \u fold varsM Kfv_p ps
    | TyData d => Kfv_d d
    end.

  Fixpoint Kfv_t (t : term) : vars :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{}
    | TmLam T t' => Kfv_ty T \u Kfv_t t'
    | TmApp t1 t2 => Kfv_t t1 \u Kfv_t t2
    | TmTyLam k t' => Kfv_k k \u Kfv_t t'
    | TmTyApp t' T => Kfv_t t' \u Kfv_ty T
    | TmFix t' => Kfv_t t'
    | TmProd t1 t2 => Kfv_t t1 \u Kfv_t t2
    | TmProj i t' => Kfv_t t'
    | TmCon K ty t' => Kfv K \u Kfv_ty ty \u Kfv_t t'
    | TmMatch t1 p t2 t3 => Kfv_t t1 \u Kfv_p p \u Kfv_t t2 \u Kfv_t t3
    | TmNever ty => Kfv_ty ty
    | TmType t' => Kfv_t t'
    | TmConDef d ty T t' => Kfv_d d \u Kfv_ty ty \u Kfv_t t'
    | TmSem ty p t' => Kfv_ty ty \u Kfv_p p \u Kfv_t t'
    | TmComp t1 t2 => Kfv_t t1 \u Kfv_t t2
    | TmSemApp t1 t2 => Kfv_t t1 \u Kfv_t t2
    end.

  (* Opening *)
  (* Opening a term replaces a bound variable by some other term. *)

  Reserved Notation "{ X ~> U } T" (at level 67).
  Fixpoint topen (X : nat) (U : type) (T : type) :=
    match T with
    | TyBVar Y => (If X = Y then U else T)
    | TyFVar _ => T
    | TyArr T1 T2 => TyArr ({X ~> U}T1) ({X ~> U}T2)
    | TyAll k T'  => TyAll k ({S X ~> U}T')
    | TyProd T1 T2 => TyProd ({X ~> U}T1) ({X ~> U}T2)
    | TyCon ty T => TyCon ({X ~> U}ty) T
    | TySem T1 T2 ps => TySem ({X ~> U}T1) ({X ~> U}T2) ps
    | TyData d => TyData d
    end
  where "{ X ~> U } T" := (topen X U T).
  #[export]
   Hint Unfold topen : mcore.

  Reserved Notation "[{ X ~> U }] t" (at level 67).
  Fixpoint topen_t (X : nat) (U : type) (t : term) :=
    match t with
    | TmBVar _ => t
    | TmFVar _ => t
    | TmLam T t' => TmLam ({X ~> U} T) ([{X ~> U}] t')
    | TmApp t1 t2 => TmApp ([{X ~> U}] t1) ([{X ~> U}] t2)
    | TmTyLam k t' => TmTyLam k ([{S X ~> U}] t')
    | TmTyApp t' T => TmTyApp ([{X ~> U}] t') ({X ~> U} T)
    | TmFix t' => TmFix ([{X ~> U}] t')
    | TmProd t1 t2 => TmProd ([{X ~> U}] t1) ([{X ~> U}] t2)
    | TmProj i t' => TmProj i ([{X ~> U}] t')
    | TmCon K ty t' => TmCon K ({X ~> U} ty) ([{X ~> U}] t')
    | TmMatch t1 p t2 t3 => TmMatch ([{X ~> U}] t1) p ([{X ~> U}] t2) ([{X ~> U}] t3)
    | TmNever ty => TmNever ({X ~> U}ty)
    | TmType t' => TmType ([{X ~> U}] t')
    | TmConDef d ty T t' => TmConDef d ({S X ~> U} ty) T ([{X ~> U}] t')
    | TmSem ty p t' => TmSem ({X ~> U} ty) p ([{X ~> U}] t')
    | TmComp t1 t2 => TmComp ([{X ~> U}] t1) ([{X ~> U}] t2)
    | TmSemApp t1 t2 => TmSemApp ([{X ~> U}] t1) ([{X ~> U}] t2)
    end
  where "[{ X ~> U }] t" := (topen_t X U t).
  #[export]
   Hint Unfold topen_t : mcore.

  Reserved Notation "[ k ~> u ] t" (at level 67).
  Fixpoint open (k : nat) (u : term) (t : term) :=
    match t with
    | TmBVar i => (If i = k then u else t)
    | TmFVar y => t
    | TmLam T t' => TmLam T ([(S k) ~> u]t')
    | TmApp t1 t2 => TmApp ([k ~> u]t1) ([k ~> u]t2)
    | TmTyLam ki t' => TmTyLam ki ([k ~> u]t')
    | TmTyApp t' T => TmTyApp ([k ~> u]t') T
    | TmFix t' => TmFix ([k ~> u]t')
    | TmProd t1 t2 => TmProd ([k ~> u]t1) ([k ~> u]t2)
    | TmProj i t' => TmProj i ([k ~> u]t')
    | TmCon K ty t' => TmCon K ty ([k ~> u]t')
    | TmMatch t1 p t2 t3 => TmMatch ([k ~> u]t1) p ([S k ~> u]t2) ([k ~> u]t3)
    | TmNever ty => TmNever ty
    | TmType t' => TmType ([k ~> u]t')
    | TmConDef d ty T t' => TmConDef d ty T ([k ~> u]t')
    | TmSem ty p t' => TmSem ty p ([S k ~> u]t')
    | TmComp t1 t2 => TmComp ([k ~> u]t1) ([k ~> u] t2)
    | TmSemApp t1 t2 => TmSemApp ([k ~> u] t1) ([k ~> u] t2)
    end
  where "[ k ~> u ] t " := (open k u t)
  .
  #[export]
   Hint Unfold open : mcore.


  Definition Topen (j : nat) (X : tname) (T : tname) :=
    match T with
    | BTName i => (If i = j then X else T)
    | FTName _ => T
    end.

  Definition Topen_d (j : nat) (X : tname) (d : data) : data :=
    LibList.map (fun '(T, Ks) => (Topen j X T, Ks)) d.

  Definition Topen_k (j : nat) (X : tname) (k : kind) :=
    match k with
    | KiType => k
    | KiData d => KiData (Topen_d j X d)
    end.

  Fixpoint Topen_ty (j : nat) (X : tname) (T : type) :=
    match T with
    | TyBVar X => T
    | TyFVar X => T
    | TyArr T1 T2 => TyArr (Topen_ty j X T1) (Topen_ty j X T2)
    | TyAll k T' => TyAll (Topen_k j X k) (Topen_ty j X T')
    | TyProd T1 T2 => TyProd (Topen_ty j X T1) (Topen_ty j X T2)
    | TyCon ty T => TyCon (Topen_ty j X ty) (Topen j X T)
    | TySem T1 T2 ps => TySem (Topen_ty j X T1) (Topen_ty j X T2) ps
    | TyData d => TyData (Topen_d j X d)
    end.

  Fixpoint Topen_t (j : nat) (X : tname) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Topen_ty j X T) (Topen_t j X t')
    | TmApp t1 t2 => TmApp (Topen_t j X t1) (Topen_t j X t2)
    | TmTyLam k t' => TmTyLam (Topen_k j X k) (Topen_t j X t')
    | TmTyApp t' T => TmTyApp (Topen_t j X t') (Topen_ty j X T)
    | TmFix t' => TmFix (Topen_t j X t')
    | TmProd t1 t2 => TmProd (Topen_t j X t1) (Topen_t j X t2)
    | TmProj i t' => TmProj i (Topen_t j X t')
    | TmCon K ty t' => TmCon K (Topen_ty j X ty) (Topen_t j X t')
    | TmMatch t1 p t2 t3 => TmMatch (Topen_t j X t1) p (Topen_t j X t2) (Topen_t j X t3)
    | TmNever ty => TmNever (Topen_ty j X ty)
    | TmType t' => TmType (Topen_t (S j) X t')
    | TmConDef d ty T t' =>
        TmConDef (Topen_d j X d) (Topen_ty j X ty) (Topen j X T) (Topen_t j X t')
    | TmSem ty p t' => TmSem (Topen_ty j X ty) p (Topen_t j X t')
    | TmComp t1 t2 => TmComp (Topen_t j X t1) (Topen_t j X t2)
    | TmSemApp t1 t2 => TmSemApp (Topen_t j X t1) (Topen_t j X t2)
    end.

  Definition Tclose (X : var) (j : nat) (T : tname) :=
    match T with
    | BTName _ => T
    | FTName Y => If X = Y then BTName j else T
    end.

  Definition Tclose_d (X : var) (j : nat) (d : data) : data :=
    LibList.map (fun '(T, Ks) => (Tclose X j T, Ks)) d.

  Definition Tclose_k (X : var) (j : nat) (k : kind) :=
    match k with
    | KiType => k
    | KiData d => KiData (Tclose_d X j d)
    end.

  Fixpoint Tclose_ty (X : var) (j : nat) (T : type) :=
    match T with
    | TyBVar Y => T
    | TyFVar Y => T
    | TyArr T1 T2 => TyArr (Tclose_ty X j T1) (Tclose_ty X j T2)
    | TyAll k T' => TyAll (Tclose_k X j k) (Tclose_ty X j T')
    | TyProd T1 T2 => TyProd (Tclose_ty X j T1) (Tclose_ty X j T2)
    | TyCon ty T => TyCon (Tclose_ty X j ty) (Tclose X j T)
    | TySem T1 T2 ps => TySem (Tclose_ty X j T1) (Tclose_ty X j T2) ps
    | TyData d => TyData (Tclose_d X j d)
    end.

  Fixpoint Tclose_t (X : var) (j : nat) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Tclose_ty X j T) (Tclose_t X j t')
    | TmApp t1 t2 => TmApp (Tclose_t X j t1) (Tclose_t X j t2)
    | TmTyLam k t' => TmTyLam (Tclose_k X j k) (Tclose_t X j t')
    | TmTyApp t' T => TmTyApp (Tclose_t X j t') (Tclose_ty X j T)
    | TmFix t' => TmFix (Tclose_t X j t')
    | TmProd t1 t2 => TmProd (Tclose_t X j t1) (Tclose_t X j t2)
    | TmProj i t' => TmProj i (Tclose_t X j t')
    | TmCon K ty t' => TmCon K (Tclose_ty X j ty) (Tclose_t X j t')
    | TmMatch t1 p t2 t3 => TmMatch (Tclose_t X j t1) p (Tclose_t X j t2) (Tclose_t X j t3)
    | TmNever ty => TmNever (Tclose_ty X j ty)
    | TmType t' => TmType (Tclose_t X (S j) t')
    | TmConDef d ty T t' =>
        TmConDef (Tclose_d X j d) (Tclose_ty X j ty) (Tclose X j T) (Tclose_t X j t')
    | TmSem ty p t' => TmSem (Tclose_ty X j ty) p (Tclose_t X j t')
    | TmComp t1 t2 => TmComp (Tclose_t X j t1) (Tclose_t X j t2)
    | TmSemApp t1 t2 => TmSemApp (Tclose_t X j t1) (Tclose_t X j t2)
    end.


  Definition Kopen_d (j : nat) (X : con) (d : data) : data :=
    LibList.map (fun '(T, Ks) => (T , LibList.map (Kopen j X) Ks)) d.

  Definition Kopen_k (j : nat) (X : con) (k : kind) :=
    match k with
    | KiType => k
    | KiData d => KiData (Kopen_d j X d)
    end.

  Fixpoint Kopen_ty (j : nat) (X : con) (T : type) :=
    match T with
    | TyBVar X => T
    | TyFVar X => T
    | TyArr T1 T2 => TyArr (Kopen_ty j X T1) (Kopen_ty j X T2)
    | TyAll k T' => TyAll (Kopen_k j X k) (Kopen_ty j X T')
    | TyProd T1 T2 => TyProd (Kopen_ty j X T1) (Kopen_ty j X T2)
    | TyCon ty T => TyCon (Kopen_ty j X ty) T
    | TySem T1 T2 ps => TySem (Kopen_ty j X T1) (Kopen_ty j X T2) (LibList.map (Kopen_p j X) ps)
    | TyData d => TyData (Kopen_d j X d)
    end.

  Fixpoint Kopen_t (j : nat) (X : con) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Kopen_ty j X T) (Kopen_t j X t')
    | TmApp t1 t2 => TmApp (Kopen_t j X t1) (Kopen_t j X t2)
    | TmTyLam k t' => TmTyLam (Kopen_k j X k) (Kopen_t j X t')
    | TmTyApp t' T => TmTyApp (Kopen_t j X t') (Kopen_ty j X T)
    | TmFix t' => TmFix (Kopen_t j X t')
    | TmProd t1 t2 => TmProd (Kopen_t j X t1) (Kopen_t j X t2)
    | TmProj i t' => TmProj i (Kopen_t j X t')
    | TmCon K ty t' => TmCon (Kopen j X K) (Kopen_ty j X ty) (Kopen_t j X t')
    | TmMatch t1 p t2 t3 =>
        TmMatch (Kopen_t j X t1) (Kopen_p j X p) (Kopen_t j X t2) (Kopen_t j X t3)
    | TmNever ty => TmNever (Kopen_ty j X ty)
    | TmType t' => TmType (Kopen_t j X t')
    | TmConDef d ty T t' =>
        TmConDef (Kopen_d j X d) (Kopen_ty j X ty) T (Kopen_t (S j) X t')
    | TmSem ty p t' => TmSem (Kopen_ty j X ty) (Kopen_p j X p) (Kopen_t j X t')
    | TmComp t1 t2 => TmComp (Kopen_t j X t1) (Kopen_t j X t2)
    | TmSemApp t1 t2 => TmSemApp (Kopen_t j X t1) (Kopen_t j X t2)
    end.

  Definition Kclose_d (X : var) (j : nat) (d : data) : data :=
    LibList.map (fun '(T, Ks) => (T, LibList.map (Kclose X j) Ks)) d.

  Definition Kclose_k (X : var) (j : nat) (k : kind) :=
    match k with
    | KiType => k
    | KiData d => KiData (Kclose_d X j d)
    end.

  Fixpoint Kclose_ty (X : var) (j : nat) (T : type) :=
    match T with
    | TyBVar Y => T
    | TyFVar Y => T
    | TyArr T1 T2 => TyArr (Kclose_ty X j T1) (Kclose_ty X j T2)
    | TyAll k T' => TyAll (Kclose_k X j k) (Kclose_ty X j T')
    | TyProd T1 T2 => TyProd (Kclose_ty X j T1) (Kclose_ty X j T2)
    | TyCon ty T => TyCon (Kclose_ty X j ty) T
    | TySem T1 T2 ps => TySem (Kclose_ty X j T1) (Kclose_ty X j T2) (LibList.map (Kclose_p X j) ps)
    | TyData d => TyData (Kclose_d X j d)
    end.

  Fixpoint Kclose_t (X : var) (j : nat) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Kclose_ty X j T) (Kclose_t X j t')
    | TmApp t1 t2 => TmApp (Kclose_t X j t1) (Kclose_t X j t2)
    | TmTyLam k t' => TmTyLam (Kclose_k X j k) (Kclose_t X j t')
    | TmTyApp t' T => TmTyApp (Kclose_t X j t') (Kclose_ty X j T)
    | TmFix t' => TmFix (Kclose_t X j t')
    | TmProd t1 t2 => TmProd (Kclose_t X j t1) (Kclose_t X j t2)
    | TmProj i t' => TmProj i (Kclose_t X j t')
    | TmCon K ty t' => TmCon (Kclose X j K) (Kclose_ty X j ty) (Kclose_t X j t')
    | TmMatch t1 p t2 t3 =>
        TmMatch (Kclose_t X j t1) (Kclose_p X j p) (Kclose_t X j t2) (Kclose_t X j t3)
    | TmNever ty => TmNever (Kclose_ty X j ty)
    | TmType t' => TmType (Kclose_t X j t')
    | TmConDef d ty T t' =>
        TmConDef (Kclose_d X j d) (Kclose_ty X j ty) T (Kclose_t X (S j) t')
    | TmSem ty p t' => TmSem (Kclose_ty X j ty) (Kclose_p X j p) (Kclose_t X j t')
    | TmComp t1 t2 => TmComp (Kclose_t X j t1) (Kclose_t X j t2)
    | TmSemApp t1 t2 => TmSemApp (Kclose_t X j t1) (Kclose_t X j t2)
    end.


  (* Local closure *)
  (* A locally closed term contains no unbound BVars. *)

  Notation lcT T := (exists T', T = FTName T').

  Definition lcd (d : data) : Prop :=
    Forall (fun '(T, Ks) => lcT T /\ Forall (fun K => lcK K) Ks) d.

  Inductive lck : kind -> Prop :=
  | LCKType : lck KiType
  | LCKData : forall d, lcd d -> lck (KiData d)
  .
  #[export]
   Hint Constructors lck : mcore.

  Inductive lct : type -> Prop :=
  | LCTFVar : forall X, lct (TyFVar X)
  | LCTArr  : forall T1 T2, lct T1 -> lct T2 -> lct (TyArr T1 T2)
  | LCTAll  : forall L k T, lck k -> (forall X, X \notin L -> lct ({0 ~> TyFVar X}T)) -> lct (TyAll k T)
  | LCTProd : forall T1 T2, lct T1 -> lct T2 -> lct (TyProd T1 T2)
  | LCTCon  : forall ty T, lct ty -> lct (TyCon ty (FTName T))
  | LCTSem  : forall T1 T2 ps, lct T1 -> lct T2 -> Forall lcp ps -> lct (TySem T1 T2 ps)
  | LCTData : forall d, lcd d -> lct (TyData d)
  .
  #[export]
   Hint Constructors lct : mcore.

  Inductive lc : term -> Prop :=
  | LCFVar   : forall x, lc (TmFVar x)
  | LCAbs    : forall L t T, lct T -> (forall x, x \notin L -> lc ([0 ~> TmFVar x]t)) -> lc (TmLam T t)
  | LCApp    : forall t1 t2, lc t1 -> lc t2 -> lc (TmApp t1 t2)
  | LCTyLam  : forall L k t, lck k -> (forall X, X \notin L -> lc ([{0 ~> TyFVar X}] t)) -> lc (TmTyLam k t)
  | LCTyApp  : forall t T, lc t -> lct T -> lc (TmTyApp t T)
  | LCFix    : forall t, lc t -> lc (TmFix t)
  | LCProd   : forall t1 t2, lc t1 -> lc t2 -> lc (TmProd t1 t2)
  | LCProj   : forall t i, lc t -> lc (TmProj i t)
  | LCCon    : forall K T t, lct T -> lc t -> lc (TmCon (FCon K) T t)
  | LCMatch  : forall L t1 p t2 t3,
      lc t1 -> lcp p ->
      (forall x, x \notin L -> lc ([0 ~> TmFVar x]t2)) ->
      lc t3 -> lc (TmMatch t1 p t2 t3)
  | LCNever  : forall ty, lct ty -> lc (TmNever ty)
  | LCType   : forall L t, (forall X, X \notin L -> lc (Topen_t 0 (FTName X) t)) -> lc (TmType t)
  | LCConDef : forall L d ty T t,
      lcd d ->
      (forall X, X \notin L -> lct ({0 ~> TyFVar X}ty)) ->
      (forall X, X \notin L -> lc (Kopen_t 0 (FCon X) t)) ->
      lc (TmConDef d ty (FTName T) t)
  | LCSem    : forall L t p ty, lct ty -> lcp p -> (forall x, x \notin L -> lc ([0 ~> TmFVar x]t)) -> lc (TmSem ty p t)
  | LCComp   : forall t1 t2, lc t1 -> lc t2 -> lc (TmComp t1 t2)
  | LCSemApp : forall t1 t2, lc t1 -> lc t2 -> lc (TmSemApp t1 t2).
  #[export]
   Hint Constructors lc : mcore.

  (* Substitution *)
  Reserved Notation "{ X => U } T" (at level 67).
  Fixpoint tsubst (X : var) (U : type) (T : type) :=
    match T with
    | TyBVar X => T
    | TyFVar Y => (If X = Y then U else T)
    | TyArr T1 T2 => TyArr ({X => U}T1) ({X => U} T2)
    | TyAll k T' => TyAll k ({X => U}T')
    | TyProd T1 T2 => TyProd ({X => U}T1) ({X => U} T2)
    | TyCon ty T => TyCon ({X => U}ty) T
    | TySem T1 T2 ps => TySem ({X => U}T1) ({X => U}T2) ps
    | TyData d => TyData d
    end
  where "{ X => U } T" := (tsubst X U T).

  Reserved Notation "[{ X => U }] t" (at level 67).

  Fixpoint tsubst_t (X : var) (U : type) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar y => t
    | TmLam T t' => TmLam ({X => U}T) ([{X => U}] t')
    | TmApp t1 t2 => TmApp ([{X => U}]t1) ([{X => U}]t2)
    | TmTyLam k t' => TmTyLam k ([{X => U}]t')
    | TmTyApp t' T => TmTyApp ([{X => U}]t') ({X => U}T)
    | TmFix t' => TmFix ([{X => U}] t')
    | TmProd t1 t2 => TmProd ([{X => U}]t1) ([{X => U}]t2)
    | TmProj i t' => TmProj i ([{X => U}] t')
    | TmCon K ty t' => TmCon K ({X => U}ty) ([{X => U}]t')
    | TmMatch t1 p t2 t3 => TmMatch ([{X => U}]t1) p ([{X => U}]t2) ([{X => U}]t3)
    | TmNever ty => TmNever ({X => U}ty)
    | TmType t' => TmType ([{X => U}]t')
    | TmConDef d ty T t' => TmConDef d ({X => U}ty) T ([{X => U}]t')
    | TmSem ty p t' => TmSem ({X => U}ty) p ([{X => U}] t')
    | TmComp t1 t2 => TmComp ([{X => U}]t1) ([{X => U}]t2)
    | TmSemApp t1 t2 => TmSemApp ([{X => U}]t1) ([{X => U}]t2)
    end
  where "[{ X => U }] t" := (tsubst_t X U t).

  Reserved Notation "[ x => u ] t" (at level 67).
  Fixpoint subst (x : var) (u : term) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar y => (If x = y then u else t)
    | TmLam T t' => TmLam T ([x => u] t')
    | TmApp t1 t2 => TmApp ([x => u]t1) ([x => u]t2)
    | TmTyLam k t' => TmTyLam k ([x => u]t')
    | TmTyApp t' T => TmTyApp ([x => u]t') T
    | TmFix t' => TmFix ([x => u]t')
    | TmProd t1 t2 => TmProd ([x => u]t1) ([x => u]t2)
    | TmProj i t' => TmProj i ([x => u]t')
    | TmCon K ty t' => TmCon K ty ([x => u]t')
    | TmMatch t1 p t2 t3 => TmMatch ([x => u]t1) p ([x => u]t2) ([x => u]t3)
    | TmNever ty => TmNever ty
    | TmType t' => TmType ([x => u]t')
    | TmConDef d ty T t' => TmConDef d ty T ([x => u]t')
    | TmSem ty p t' => TmSem ty p ([x => u] t')
    | TmComp t1 t2 => TmComp ([x => u]t1) ([x => u]t2)
    | TmSemApp t1 t2 => TmSemApp ([x => u]t1) ([x => u]t2)
    end
  where "[ x => u ] t" := (subst x u t).
  #[export]
   Hint Unfold subst : mcore.


  Definition Tsubst (X : var) (U : tname) (T : tname) :=
    match T with
    | BTName _ => T
    | FTName Y => (If X = Y then U else T)
    end.

  Definition Tsubst_d (X : var) (U : tname) (d : data) : data :=
    LibList.map (fun '(T, Ks) => (Tsubst X U T, Ks)) d.

  Definition Tsubst_k (X : var) (U : tname) (k : kind) :=
    match k with
    | KiType => k
    | KiData d => KiData (Tsubst_d X U d)
    end.

  Fixpoint Tsubst_ty (X : var) (U : tname) (T : type) :=
    match T with
    | TyBVar X => T
    | TyFVar X => T
    | TyArr T1 T2 => TyArr (Tsubst_ty X U T1) (Tsubst_ty X U T2)
    | TyAll k T' => TyAll (Tsubst_k X U k) (Tsubst_ty X U T')
    | TyProd T1 T2 => TyProd (Tsubst_ty X U T1) (Tsubst_ty X U T2)
    | TyCon ty T => TyCon (Tsubst_ty X U ty) (Tsubst X U T)
    | TyData d => TyData (Tsubst_d X U d)
    | TySem T1 T2 ps => TySem (Tsubst_ty X U T1) (Tsubst_ty X U T2) ps
    end.

  Fixpoint Tsubst_t (X : var) (U : tname) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Tsubst_ty X U T) (Tsubst_t X U t')
    | TmApp t1 t2 => TmApp (Tsubst_t X U t1) (Tsubst_t X U t2)
    | TmTyLam k t' => TmTyLam (Tsubst_k X U k) (Tsubst_t X U t')
    | TmTyApp t' T => TmTyApp (Tsubst_t X U t') (Tsubst_ty X U T)
    | TmFix t' => TmFix (Tsubst_t X U t')
    | TmProd t1 t2 => TmProd (Tsubst_t X U t1) (Tsubst_t X U t2)
    | TmProj i t' => TmProj i (Tsubst_t X U t')
    | TmCon K ty t' => TmCon K (Tsubst_ty X U ty) (Tsubst_t X U t')
    | TmMatch t1 p t2 t3 =>
        TmMatch (Tsubst_t X U t1) p (Tsubst_t X U t2) (Tsubst_t X U t3)
    | TmNever ty => TmNever (Tsubst_ty X U ty)
    | TmType t' => TmType (Tsubst_t X U t')
    | TmConDef d ty T t' =>
        TmConDef (Tsubst_d X U d) (Tsubst_ty X U ty) (Tsubst X U T) (Tsubst_t X U t')
    | TmSem ty p t' => TmSem (Tsubst_ty X U ty) p (Tsubst_t X U t')
    | TmComp t1 t2 => TmComp (Tsubst_t X U t1) (Tsubst_t X U t2)
    | TmSemApp t1 t2 => TmSemApp (Tsubst_t X U t1) (Tsubst_t X U t2)
    end.


  Definition Ksubst_d (X : var) (U : con) (d : data) : data :=
    LibList.map (fun '(T, Ks) => (T, LibList.map (Ksubst X U) Ks)) d.

  Definition Ksubst_k (X : var) (U : con) (k : kind) :=
    match k with
    | KiType => k
    | KiData d => KiData (Ksubst_d X U d)
    end.

  Fixpoint Ksubst_ty (X : var) (U : con) (T : type) :=
    match T with
    | TyBVar X => T
    | TyFVar X => T
    | TyArr T1 T2 => TyArr (Ksubst_ty X U T1) (Ksubst_ty X U T2)
    | TyAll k T' => TyAll (Ksubst_k X U k) (Ksubst_ty X U T')
    | TyProd T1 T2 => TyProd (Ksubst_ty X U T1) (Ksubst_ty X U T2)
    | TyCon ty T => TyCon (Ksubst_ty X U ty) T
    | TySem T1 T2 ps => TySem (Ksubst_ty X U T1) (Ksubst_ty X U T2) (LibList.map (Ksubst_p X U) ps)
    | TyData d => TyData (Ksubst_d X U d)
    end.

  Fixpoint Ksubst_t (X : var) (U : con) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Ksubst_ty X U T) (Ksubst_t X U t')
    | TmApp t1 t2 => TmApp (Ksubst_t X U t1) (Ksubst_t X U t2)
    | TmTyLam k t' => TmTyLam (Ksubst_k X U k) (Ksubst_t X U t')
    | TmTyApp t' T => TmTyApp (Ksubst_t X U t') (Ksubst_ty X U T)
    | TmFix t' => TmFix (Ksubst_t X U t')
    | TmProd t1 t2 => TmProd (Ksubst_t X U t1) (Ksubst_t X U t2)
    | TmProj i t' => TmProj i (Ksubst_t X U t')
    | TmCon K ty t' => TmCon (Ksubst X U K) (Ksubst_ty X U ty) (Ksubst_t X U t')
    | TmMatch t1 p t2 t3 =>
        TmMatch (Ksubst_t X U t1) (Ksubst_p X U p) (Ksubst_t X U t2) (Ksubst_t X U t3)
    | TmNever ty => TmNever (Ksubst_ty X U ty)
    | TmType t' => TmType (Ksubst_t X U t')
    | TmConDef d ty T t' =>
        TmConDef (Ksubst_d X U d) (Ksubst_ty X U ty) T (Ksubst_t X U t')
    | TmSem ty p t' => TmSem (Ksubst_ty X U ty) (Ksubst_p X U p) (Ksubst_t X U t')
    | TmComp t1 t2 => TmComp (Ksubst_t X U t1) (Ksubst_t X U t2)
    | TmSemApp t1 t2 => TmSemApp (Ksubst_t X U t1) (Ksubst_t X U t2)
    end.


  (*****************************)
  (** ENVIRONMENT DEFINITIONS **)
  (*****************************)

  Inductive binding : Type :=
  | BindTName   : binding
  | BindCon     : data -> type -> tname -> binding
  | BindTVar    : kind -> binding
  | BindVar     : type -> binding
  | BindMatch   : term -> pat -> bool -> binding.

  Definition env := env binding.

  Definition bsubst (x : var) (u : term) (b : binding) :=
    match b with
    | BindMatch t p m => BindMatch ([x => u]t) p m
    | _ => b
    end.

  Definition tbsubst (X : var) (U : type) (b : binding) :=
    match b with
    | BindVar T => BindVar ({X => U} T)
    | BindCon d ty T => BindCon d ({X => U} ty) T
    | BindMatch t p m => BindMatch ([{X => U}]t) p m
    | _ => b
    end.

  Definition Tbsubst (X : var) (U : tname) (b : binding) :=
    match b with
    | BindVar T => BindVar (Tsubst_ty X U T)
    | BindTVar k => BindTVar (Tsubst_k X U k)
    | BindCon d ty T => BindCon (Tsubst_d X U d) (Tsubst_ty X U ty) (Tsubst X U T)
    | BindMatch t p m => BindMatch (Tsubst_t X U t) p m
    | _ => b
    end.

  Definition Kbsubst (X : var) (U : con) (b : binding) :=
    match b with
    | BindVar T => BindVar (Ksubst_ty X U T)
    | BindTVar k => BindTVar (Ksubst_k X U k)
    | BindCon d ty T => BindCon (Ksubst_d X U d) (Ksubst_ty X U ty) T
    | BindMatch t p m => BindMatch (Ksubst_t X U t) (Ksubst_p X U p) m
    | _ => b
    end.

  (**********************************)
  (** TACTICS FOR LOCALLY NAMELESS **)
  (**********************************)

  Ltac gather_vars :=
    let A := gather_vars_with (fun x : vars => x) in
    let B := gather_vars_with (fun x : var => \{x}) in
    let C := gather_vars_with (fun x : env => dom x) in
    let D := gather_vars_with (fun x : term => fv x) in
    let E := gather_vars_with (fun x : term => tfv_t x) in
    let F := gather_vars_with (fun x : term => Tfv_t x) in
    let G := gather_vars_with (fun x : term => Kfv_t x) in
    let H := gather_vars_with (fun x : type => tfv x) in
    let I := gather_vars_with (fun x : type => Tfv_ty x) in
    let J := gather_vars_with (fun x : type => Kfv_ty x) in
    let K := gather_vars_with (fun x : kind => Tfv_k x) in
    let L := gather_vars_with (fun x : kind => Kfv_k x) in
    let M := gather_vars_with (fun x : data => Tfv_d x) in
    let N := gather_vars_with (fun x : data => Kfv_d x) in
    let O := gather_vars_with (fun x : con  => Kfv x) in
    let P := gather_vars_with (fun x : tname => Tfv x) in
    let Q := gather_vars_with (fun x : pat  => Kfv_p x) in
    constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K \u L \u M \u N \u O \u P \u Q).

  Ltac pick_fresh x :=
    let L := gather_vars in (pick_fresh_gen L x).

  Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
    apply_fresh_base T gather_vars x.

  Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
    apply_fresh T as x; intuition eauto.
  Tactic Notation "apply_fresh" constr(T) :=
    apply_fresh_base T gather_vars ltac_no_arg.
  Tactic Notation "apply_fresh" "*" constr(T) :=
    apply_fresh T; auto_star.

End Syntax.
