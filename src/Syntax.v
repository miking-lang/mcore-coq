From TLC Require Import LibString LibLogic LibSet LibMap LibNat.
From MCore Require Import Tactics.

Open Scope nat_scope.

Module Type PAT.
  Parameter pat : Type.
End PAT.

Module Syntax (P : PAT).
  Export P.

  (************************)
  (** SYNTAX DEFINITIONS **)
  (************************)

  Definition var   : Set := nat.
  Definition bvar  : Set := nat.
  Definition tname : Set := var.
  Definition con   : Set := var.
  Definition data  : Type := map tname (set con).

  Inductive kind : Type :=
  | KiType : kind
  (* | KiData : data -> kind *)
  .

  Inductive type : Type :=
  | TyBVar : bvar -> type
  | TyFVar : var  -> type
  | TyArr  : type -> type -> type
  | TyAll  : kind -> type -> type
  (* | TyProd : type -> type -> type *)
  (* | TyCon  : type -> tname -> type *)
  (* | TySem  : type -> type -> list pat -> type *)
  (* | TyData : data -> type *)
  .

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
  Proof. apply (Inhab_of_val (TmBVar 0)). Qed.


  (**************************)
  (** OPERATIONS ON SYNTAX **)
  (**************************)

  (* Notation scheme:
     - curly braces indicate type-level operations, and square braces indicate term-level ones
     - curly arrows indicate operations on bound variables, and double ones indicate free variables
     - type-level operations generally start with t
     - type-level operations working over terms are suffixed by _t
   *)

  (* Opening *)
  (* Opening a term replaces a bound variable by some other term. *)

  Reserved Notation "{ X ~> U } T" (at level 67).
  Fixpoint topen (X : nat) (U : type) (T : type) :=
    match T with
    | TyBVar Y => (If X = Y then U else T)
    | TyFVar _ => T
    | TyArr T1 T2 => TyArr ({X ~> U}T1) ({X ~> U}T2)
    | TyAll k T'  => TyAll k ({S X ~> U}T')
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
    end
  where "[ k ~> u ] t " := (open k u t)
  .
  #[export]
   Hint Unfold open : mcore.

  (* Substitution *)

  Reserved Notation "{ X => U } T" (at level 67).
  Fixpoint tsubst (X : var) (U : type) (T : type) :=
    match T with
    | TyBVar X => T
    | TyFVar Y => (If X = Y then U else T)
    | TyArr T1 T2 => TyArr ({X => U}T1) ({X => U} T2)
    | TyAll k T' => TyAll k ({X => U}T')
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
    end
  where "[ x => u ] t" := (subst x u t).
  #[export]
   Hint Unfold subst : mcore.

  (**************************)
  (** PROPERTIES OF SYNTAX **)
  (**************************)

  (* Freshness *)

  Fixpoint tfresh (Y : var) (T : type) :=
    match T with
    | TyBVar X => True
    | TyFVar X => X <> Y
    | TyArr T1 T2 => tfresh Y T1 /\ tfresh Y T2
    | TyAll k T' => tfresh Y T'
    end
  .

  Fixpoint tfresh_t (Y : var) (t : term) :=
    match t with
    | TmBVar i => False
    | TmFVar x => False
    | TmLam T t' => tfresh Y T /\ tfresh_t Y t'
    | TmApp t1 t2 => tfresh_t Y t1 /\ tfresh_t Y t2
    | TmTyLam k t' => tfresh_t Y t'
    | TmTyApp t' T => tfresh_t Y t' /\ tfresh Y T
    end
  .

  Fixpoint fresh (y : var) (t : term) :=
    match t with
    | TmBVar i => False
    | TmFVar x => x <> y
    | TmLam T t' => fresh y t'
    | TmApp t1 t2 => fresh y t1 /\ fresh y t2
    | TmTyLam k t' => fresh y t'
    | TmTyApp t' T => fresh y t'
    end
  .

  (* Local closure *)
  (* A locally closed term contains no unbound BVars. *)

  Inductive lct : type -> Prop :=
  | LCTFVar : forall X, lct (TyFVar X)
  | LCTArr  : forall T1 T2, lct T1 -> lct T2 -> lct (TyArr T1 T2)
  | LCTAll  : forall X k T, lct ({0 ~> TyFVar X}T) -> lct (TyAll k T)
  .
  #[export]
   Hint Constructors lct : mcore.

  Inductive lc : term -> Prop :=
  | LCFVar  : forall x, lc (TmFVar x)
  | LCAbs   : forall x t T, lct T -> lc ([0 ~> TmFVar x]t) -> lc (TmLam T t)
  | LCApp   : forall t1 t2, lc t1 -> lc t2 -> lc (TmApp t1 t2)
  | LCTyLam  : forall X k t, lc ([{0 ~> TyFVar X}] t) -> lc (TmTyLam k t)
  | LCTyApp  : forall t T, lc t -> lct T -> lc (TmTyApp t T)
  .
  #[export]
   Hint Constructors lc : mcore.

  Lemma topen_neq :
    forall I J U V T,
      I <> J ->
      {I ~> U}({J ~> V}T) = {J ~> V}T ->
      {I ~> U}T = T.
  Proof.
    introv Hneq Heq. gen I J.
    simple_eq T; inverts* Heq.
  Qed.

  Lemma topen_lct :
    forall K U T,
      lct T ->
      {K ~> U}T = T.
  Proof.
    introv Hlct. gen K.
    simple_eq Hlct.
    rewrite topen_neq with (J := 0) (V := TyFVar X);
      auto.
  Qed.

  Lemma tsubst_topen_distr :
    forall X U k T1 T2,
      lct U ->
      {X => U} ({k ~> T2}T1) = {k ~> {X => U}T2} ({X => U}T1).
  Proof.
    introv Hlct. gen k.
    simple_eq T1. rewrite* topen_lct.
  Qed.

  Lemma tsubst_fresh :
    forall X T U,
      tfresh X T ->
      {X => U}T = T.
  Proof. introv Hfv ; simple_eq T. Qed.

  Lemma tsubst_intro :
    forall X T U,
      tfresh X T ->
      lct U ->
      {0 ~> U} T = {X => U}({0 ~> TyFVar X}T).
  Proof.
    introv Hfv Hlc.
    rewrite* tsubst_topen_distr.
    simple_math. rewrite* tsubst_fresh.
  Qed.

  Lemma tsubst_topen_comm :
    forall X Y U T n,
      X <> Y ->
      lct U ->
      {n ~> TyFVar Y} ({X => U}T) = {X => U} ({n ~> TyFVar Y} T).
  Proof.
    introv Hneq Hlct. gen n.
    simple_eq T ; rewrite* topen_lct.
  Qed.

  Lemma tsubst_lct :
    forall X U T,
      lct T ->
      lct U ->
      lct ({X => U}T).
  Proof with simple_math.
    introv Hlct1 Hlct2.
    induction Hlct1...
    - admit.
      (* apply (LCTAll (Nat.max X X0)). intros. *)
      (* rewrite tsubst_topen_comm... apply H0... *)
  Admitted.

  Lemma open_neq :
    forall i j u v t,
      i <> j ->
      [i ~> u]([j ~> v]t) = [j ~> v]t ->
      [i ~> u]t = t.
  Proof.
    introv Hneq Heq. gen i j. simple_eq t ; inverts* Heq.
  Qed.

  Lemma open_topen_neq :
    forall i u J V t,
      [i ~> u]([{J ~> V}]t) = [{J ~> V}] t ->
      [i ~> u]t = t.
  Proof.
    introv Heq. gen i J. simple_eq t ; inverts* Heq.
  Qed.

  Lemma open_lc :
    forall k u t,
      lc t ->
      [k ~> u]t = t.
  Proof.
    introv Hlc. gen k.
    simple_eq Hlc.
    - rewrite open_neq with (j := 0) (v := TmFVar x);
        auto.
    - rewrite open_topen_neq with (J := 0) (V := TyFVar X);
        auto.
  Qed.

  Lemma subst_open_distr :
    forall x u t1 t2,
      lc u ->
      [x => u] ([0 ~> t2] t1) = [0 ~> [x => u]t2]([x => u]t1).
  Proof.
    introv Hlc. generalize 0.
    simple_eq t1. rewrite* open_lc.
  Qed.

  Lemma subst_open_comm :
    forall x y u t,
      x <> y ->
      lc u ->
      [0 ~> TmFVar y]([x => u]t) = [x => u] ([0 ~> TmFVar y]t).
  Proof.
    introv Hneq Hlc. generalize 0.
    simple_eq t. apply* open_lc.
  Qed.

  Lemma subst_fresh :
    forall x t u,
      fresh x t ->
      [x => u]t = t.
  Proof. simple_eq t. Qed.

  Lemma subst_intro :
    forall x t u,
      fresh x t ->
      [0 ~> u] t = [x => u]([0 ~> TmFVar x]t).
  Proof.
    introv Hfv. unfolds.
    generalize 0. simple_eq t.
  Qed.

  Lemma tsubst_t_topen_distr :
    forall X U T t,
      lct U ->
      [{X => U}] ([{0 ~> T}] t) = [{0 ~> {X => U}T}] ([{X => U}]t).
  Proof.
    introv Hlct.
    generalize 0. simple_eq t ;
      apply* tsubst_topen_distr.
  Qed.

  Lemma tsubst_t_fresh :
    forall X t U,
      tfresh_t X t ->
      [{X => U}]t = t.
  Proof.
    introv Hfv.
    simple_eq t; apply* tsubst_fresh.
  Qed.

  Lemma tsubst_t_intro :
    forall X U t,
      tfresh_t X t ->
      lct U ->
      [{0 ~> U}]t = [{X => U}] ([{0 ~> TyFVar X}]t).
  Proof.
    introv Hftv Hlc.
    rewrite* tsubst_t_topen_distr.
    simple_math. rewrite* tsubst_t_fresh.
  Qed.

  Lemma topen_open_rec :
    forall n T t x,
      [{n ~> T}] ([0 ~> TmFVar x] t) = [0 ~> TmFVar x]t ->
      [{n ~> T}] t = t.
  Proof.
    introv Heq. generalize dependent 0. gen n.
    simple_eq t ; inverts* Heq.
  Qed.

  Lemma topen_t_rec :
    forall I J T U t,
      I <> J ->
      [{I ~> T}] ([{J ~> U}] t) = [{J ~> U}] t ->
      [{I ~> T}]t = t.
  Proof.
    introv Hneq Heq. gen I J.
    simple_eq t ; inverts* Heq; eauto using topen_neq.
  Qed.

  Lemma topen_t_lc :
    forall T t n,
      lc t ->
      [{n ~> T}]t = t.
  Proof.
    introv Hlc. gen n.
    simple_eq Hlc.
    - rewrite* topen_lct.
    - applys* topen_open_rec x.
    - rewrite* (@topen_t_rec (S n) 0 T (TyFVar X)).
    - rewrite* topen_lct.
  Qed.

  Lemma topen_t_subst_comm :
    forall X x t1 t2,
      lc t2 ->
      [{0 ~> TyFVar X}] ([x => t2]t1) = [x => t2]([{0 ~> TyFVar X}] t1).
  Proof.
    introv Hlc. generalize 0.
    simple_eq t1. rewrite* topen_t_lc.
  Qed.

  Lemma tsubst_t_open_comm :
    forall X x U t,
      [0 ~> TmFVar x] ([{X => U}]t) = [{X => U}] ([0 ~> TmFVar x]t).
  Proof. introv. generalize 0. simple_eq t. Qed.

  Lemma topen_notin :
    forall T X Y,
      tfresh X ({0 ~> TyFVar Y}T) ->
      tfresh X T.
  Proof.
    introv Hnin. generalize dependent 0.
    induction T; intros; simpls*.
  Qed.

  Lemma topen_t_tsubst_comm :
    forall X Y T t,
      X <> Y ->
      lct T ->
      [{0 ~> TyFVar Y}] ([{X => T}]t) =
        [{X => T}]([{0 ~> TyFVar Y}] t).
  Proof.
    introv Hneq Hlct. generalize dependent 0.
    simple_eq t ; rewrite* tsubst_topen_comm.
  Qed.

End Syntax.
