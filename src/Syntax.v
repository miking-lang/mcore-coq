From TLC Require Import LibString LibLN LibEnv.
From MCore Require Import Tactics.

Module Type PAT.
  Parameter pat : Type.
End PAT.

Module Syntax (P : PAT).
  Export P.

  (************************)
  (** SYNTAX DEFINITIONS **)
  (************************)

  Definition bvar  : Set := nat.
  Definition tname : Set := var.
  Definition con   : Set := var.
  Definition data  : Type := env vars.

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
     - type-level operation names generally start with t
     - type-level operations working over terms are suffixed by _t
   *)

  (* Free variables *)

  Fixpoint ftv (T : type) :=
    match T with
    | TyBVar X => \{}
    | TyFVar X => \{X}
    | TyArr T1 T2 => ftv T1 \u ftv T2
    | TyAll k T' => ftv T'
    end
  .

  Fixpoint ftv_t (t : term) :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{}
    | TmLam T t' => ftv T \u ftv_t t'
    | TmApp t1 t2 => ftv_t t1 \u ftv_t t2
    | TmTyLam k t' => ftv_t t'
    | TmTyApp t' T => ftv_t t' \u ftv T
    end
  .

  Fixpoint fv (t : term) :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{x}
    | TmLam T t' => fv t'
    | TmApp t1 t2 => fv t1 \u fv t2
    | TmTyLam k t' => fv t'
    | TmTyApp t' T => fv t'
    end
  .

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

  (* Local closure *)
  (* A locally closed term contains no unbound BVars. *)

  Inductive lct : type -> Prop :=
  | LCTFVar : forall X, lct (TyFVar X)
  | LCTArr  : forall T1 T2, lct T1 -> lct T2 -> lct (TyArr T1 T2)
  | LCTAll : forall L k T, (forall X, X \notin L -> lct ({0 ~> TyFVar X}T)) -> lct (TyAll k T)
  .
  #[export]
   Hint Constructors lct : mcore.

  Inductive lc : term -> Prop :=
  | LCFVar  : forall x, lc (TmFVar x)
  | LCAbs   : forall L t T, lct T -> (forall x, x \notin L -> lc ([0 ~> TmFVar x]t)) -> lc (TmLam T t)
  | LCApp   : forall t1 t2, lc t1 -> lc t2 -> lc (TmApp t1 t2)
  | LCTyLam  : forall L k t, (forall X, X \notin L -> lc ([{0 ~> TyFVar X}] t)) -> lc (TmTyLam k t)
  | LCTyApp  : forall t T, lc t -> lct T -> lc (TmTyApp t T)
  .
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


  (*****************************)
  (** ENVIRONMENT DEFINITIONS **)
  (*****************************)

  Inductive match_assum : Type :=
  | Match   : term -> pat -> match_assum
  | NoMatch : term -> pat -> match_assum
  .

  Inductive binding : Type :=
  | BindTName : binding
  | BindCon   : data -> type -> tname -> binding
  | BindTVar  : kind -> binding
  | BindVar   : type -> binding
  | BindMatch : match_assum -> binding
  .

  Definition env := env binding.


  (**********************************)
  (** TACTICS FOR LOCALLY NAMELESS **)
  (**********************************)

  Ltac gather_vars :=
    let A := gather_vars_with (fun x : vars => x) in
    let B := gather_vars_with (fun x : var => \{x}) in
    let C := gather_vars_with (fun x : env => dom x) in
    let D := gather_vars_with (fun x : term => fv x) in
    let E := gather_vars_with (fun x : term => ftv_t x) in
    let F := gather_vars_with (fun x : type => ftv x) in
    constr:(A \u B \u C \u D \u E \u F).

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


  (******************************)
  (** PROPERTIES OF OPERATIONS **)
  (******************************)

  Lemma topen_neq :
    forall I J U V T,
      I <> J ->
      {I ~> U}({J ~> V}T) = {J ~> V}T ->
      {I ~> U}T = T.
  Proof.
    introv Hneq Heq. gen I J.
    induction *T; intros; inverts Heq; simpls; fequals*.
    - case_nat*. case_nat*.
  Qed.

  Lemma topen_lct :
    forall K U T,
      lct T ->
      {K ~> U}T = T.
  Proof.
    introv Hlct. gen K.
    induction Hlct; intros; simpls; fequals*.
    - unfolds topen.
      pick_fresh x.
      rewrite topen_neq with (J := 0) (V := TyFVar x);
        auto.
  Qed.

  Lemma tsubst_topen_distr :
    forall X U k T1 T2,
      lct U ->
      {X => U} ({k ~> T2}T1) = {k ~> {X => U}T2} ({X => U}T1).
  Proof.
    introv Hlct. gen k.
    induction T1; intros; simpls*; fequals*.
    + case_nat*.
    + case_var*.
      rewrite* topen_lct.
  Qed.

  Lemma tsubst_fresh :
    forall X T U,
      X \notin ftv T ->
      {X => U}T = T.
  Proof.
    introv Hfv.
    induction T; simpls; fequals*.
    - case_var*.
  Qed.

  Lemma tsubst_intro :
    forall X T U,
      X \notin (ftv T) ->
      lct U ->
      {0 ~> U} T = {X => U}({0 ~> TyFVar X}T).
  Proof.
    introv Hfv Hlc.
    unfolds. rewrite* tsubst_topen_distr.
    simpls. case_var. rewrite* tsubst_fresh.
  Qed.

  Lemma tsubst_topen_comm :
    forall X Y U T n,
      X <> Y ->
      lct U ->
      {n ~> TyFVar Y} ({X => U}T) = {X => U} ({n ~> TyFVar Y} T).
  Proof.
    introv Hneq Hlct. gen n.
    induction *T; intros; simpls; fequals*.
    - case_nat*. unfolds tsubst. case_var*.
    - case_var*. rewrite* topen_lct.
  Qed.

  Lemma tsubst_lct :
    forall X U T,
      lct T ->
      lct U ->
      lct ({X => U}T).
  Proof.
    introv Hlct1 Hlct2.
    induction* Hlct1; simpls*.
    - case_var*.
    - apply_fresh* LCTAll.
      unfolds topen.
      rewrite* tsubst_topen_comm.
  Qed.

  Lemma open_neq :
    forall i j u v t,
      i <> j ->
      [i ~> u]([j ~> v]t) = [j ~> v]t ->
      [i ~> u]t = t.
  Proof.
    introv Hneq Heq. gen i j. unfolds open.
    induction *t; intros; inverts Heq; simpls; fequals*.
    - case_if* in H0. case_if*.
  Qed.

  Lemma open_topen_neq :
    forall i u J V t,
      [i ~> u]([{J ~> V}]t) = [{J ~> V}] t ->
      [i ~> u]t = t.
  Proof.
    introv Heq. gen i J.
    induction *t; intros; inverts Heq; simpls; fequals*.
  Qed.

  Lemma open_lc :
    forall k u t,
      lc t ->
      [k ~> u]t = t.
  Proof.
    introv Hlc. gen k.
    induction Hlc; intros; simpls; fequals*.
    - unfolds open.
      pick_fresh x.
      rewrite open_neq with (j := 0) (v := TmFVar x);
        auto.
    - pick_fresh X.
      rewrite open_topen_neq with (J := 0) (V := TyFVar X);
        auto.
  Qed.

  Lemma subst_open_distr :
    forall x u t1 t2,
      lc u ->
      [x => u] ([0 ~> t2] t1) = [0 ~> [x => u]t2]([x => u]t1).
  Proof.
    introv Hlc.
    unfolds open. generalize 0.
    induction t1; intros; simpls*; fequals*.
    - case_if*.
    - case_var*.
      rewrite* open_lc.
  Qed.

  (* Lemma subst_open_comm : *)
  (*   forall x y u t, *)
  (*     x <> y -> *)
  (*     lc u -> *)
  (*     ([x ~> u]t) ^ y = [x ~> u] (t ^ y). *)
  (* Proof. *)
  (*   introv Hneq Hlc. *)
  (*   unfolds. generalize 0. *)
  (*   induction *t; intros; simpl_open; fequals*; *)
  (*     eauto using open_lc. *)
  (*   - unfolds subst. case_var*. *)
  (* Qed. *)

  (* Lemma subst_fresh : *)
  (*   forall x t u, *)
  (*     x \notin fv t -> *)
  (*     [x ~> u]t = t. *)
  (* Proof. *)
  (*   introv Hfv. *)
  (*   induction t; simpls; fequals*. *)
  (*   - case_var*. *)
  (* Qed. *)

  (* Lemma subst_intro : *)
  (*   forall x t u, *)
  (*     x \notin (fv t) -> *)
  (*     t ^^ u = [x ~> u](t ^ x). *)
  (* Proof. *)
  (*   introv Hfv. unfolds. *)
  (*   generalize 0. *)
  (*   induction t; intros ; simpls; fequals*. *)
  (*   - case_if*. simpls. case_if*. *)
  (*   - case_var*. *)
  (* Qed. *)

  (* Lemma tsubst_t_topen_distr : *)
  (*   forall X U T t, *)
  (*     lct U -> *)
  (*     [[X ~> U]] (topen_t T t) = topen_t ([{X ~> U}]T) ([[X ~> U]]t). *)
  (* Proof. *)
  (*   introv Hlct. *)
  (*   unfolds topen_t. generalize 0. *)
  (*   induction t; intros; simpls*; fequals*; *)
  (*     eauto using tsubst_topen_distr. *)
  (* Qed. *)

  (* Lemma tsubst_t_fresh : *)
  (*   forall X t U, *)
  (*     X \notin ftv_t t -> *)
  (*     [[X ~> U]]t = t. *)
  (* Proof. *)
  (*   introv Hfv. *)
  (*   induction t; simpls; fequals*; *)
  (*     eauto using tsubst_fresh. *)
  (* Qed. *)

  (* Lemma tsubst_t_intro : *)
  (*   forall X U t, *)
  (*     X \notin (ftv_t t) -> *)
  (*     lct U -> *)
  (*     topen_t U t = [[X ~> U]] (topen_t (TFVar X) t). *)
  (* Proof. *)
  (*   introv Hftv Hlc. *)
  (*   unfolds. rewrite* tsubst_t_topen_distr. *)
  (*   simpls. case_var. rewrite* tsubst_t_fresh. *)
  (* Qed. *)

  (* Lemma topen_open_rec : *)
  (*   forall n T t x, *)
  (*     topen_t' n T (t ^ x) = t ^ x -> *)
  (*     topen_t' n T t = t. *)
  (* Proof. *)
  (*   introv Heq. unfolds open. generalize dependent 0. gen n. *)
  (*   induction t; intros; simpls*; inverts Heq; fequals*. *)
  (* Qed. *)

  (* Lemma topen_t_rec : *)
  (*   forall i j T U t, *)
  (*     i <> j -> *)
  (*     topen_t' i T (topen_t' j U t) = (topen_t' j U t) -> *)
  (*     (topen_t' i T t) = t. *)
  (* Proof with eauto using topen_neq. *)
  (*   introv Hneq Heq. gen i j. *)
  (*   induction t; intros; simpls*; inverts *Heq; fequals... *)
  (* Qed. *)

  (* Lemma topen_t_lc : *)
  (*   forall T t n, *)
  (*     lc t -> *)
  (*     topen_t' n T t = t. *)
  (* Proof. *)
  (*   introv Hlc. gen n. *)
  (*   induction Hlc; intros; simpls; fequals*. *)
  (*   - rewrite* topen_lct. *)
  (*   - pick_fresh_gen L x. apply* topen_open_rec. *)
  (*   - pick_fresh_gen L x. *)
  (*     rewrite* (@topen_t_rec (S n) 0 T (TFVar x)). *)
  (*   - rewrite* topen_lct. *)
  (* Qed. *)

End Syntax.
