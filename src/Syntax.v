From TLC Require Import LibString LibList LibLN.
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

  Inductive tname : Set :=
  | BTName : bvar -> tname
  | FTName : var  -> tname
  .

  Inductive con : Set :=
  | BCon : bvar -> con
  | FCon : var  -> con
  .

  Definition data : Type :=
    list (tname * list con).

  Inductive kind : Type :=
  | KiType : kind
  | KiData : data -> kind
  .

  Inductive type : Type :=
  | TyBVar : bvar -> type
  | TyFVar : var  -> type
  | TyArr  : type -> type -> type
  | TyAll  : kind -> type -> type
  (* | TyProd : type -> type -> type *)
  | TyCon  : type -> tname -> type
  (* | TySem  : type -> type -> list pat -> type *)
  | TyData : data -> type
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
  | TmCon    : con -> type -> term -> term
  (* | TmMatch  : term -> pat -> term -> term -> term *)
  (* | TmNever  : term *)
  | TmType   : term -> term
  | TmConDef : data -> type -> tname -> term -> term
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

  Definition Tfv (T : tname) :=
    match T with
    | BTName X => \{}
    | FTName X => \{X}
    end
  .

  Definition Kfv (K : con) :=
    match K with
    | BCon X => \{}
    | FCon X => \{X}
    end
  .

  Definition dfv (d : data) : vars :=
    fold_right
      (fun '(T,Ks) fvs =>
         Tfv T \u
         fold_right (fun con fvs' => Kfv con \u fvs') \{} Ks)
      \{}
      d.

  Definition kfv (k : kind) : vars :=
    match k with
    | KiType => \{}
    | KiData d => dfv d
    end.

  Fixpoint tfv (T : type) : vars :=
    match T with
    | TyBVar X => \{}
    | TyFVar X => \{X}
    | TyArr T1 T2 => tfv T1 \u tfv T2
    | TyAll k T' => kfv k \u tfv T'
    | TyCon ty T => tfv ty \u Tfv T
    | TyData d => dfv d
    end.

  Fixpoint fv (t : term) : vars :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{x}
    | TmLam T t' => tfv T \u fv t'
    | TmApp t1 t2 => fv t1 \u fv t2
    | TmTyLam k t' => kfv k \u fv t'
    | TmTyApp t' T => fv t' \u tfv T
    | TmCon K ty t' => Kfv K \u tfv ty \u fv t'
    | TmType t' => fv t'
    | TmConDef d ty T t' => dfv d \u tfv ty \u Tfv T \u fv t'
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
    | TyCon ty T => TyCon ({X ~> U}ty) T
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
    | TmCon K ty t' => TmCon K ({X ~> U}ty) ([{X ~> U}]t')
    | TmType t' => TmType ([{X ~> U}]t')
    | TmConDef d ty T t' => TmConDef d ({X ~> U}ty) T ([{X ~> U}]t')
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
    | TmCon K ty t' => TmCon K ty ([k ~> u]t')
    | TmType t' => TmType ([k ~> u]t')
    | TmConDef d ty T t' => TmConDef d ty T ([k ~> u]t')
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
    | TyCon ty T => TyCon (Topen_ty j X ty) (Topen j X T)
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
    | TmCon K ty t' => TmCon K (Topen_ty j X ty) (Topen_t j X t')
    | TmType t' => TmType (Topen_t (S j) X t')
    | TmConDef d ty T t' =>
        TmConDef (Topen_d j X d) (Topen_ty j X ty) (Topen j X T) (Topen_t j X t')
    end.


  Definition Kopen (j : nat) (X : con) (K : con) :=
    match K with
    | BCon i => (If i = j then X else K)
    | FCon _ => K
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
    | TyCon ty T => TyCon (Kopen_ty j X ty) T
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
    | TmCon K ty t' => TmCon (Kopen j X K) (Kopen_ty j X ty) (Kopen_t j X t')
    | TmType t' => TmType (Kopen_t j X t')
    | TmConDef d ty T t' =>
        TmConDef (Kopen_d j X d) (Kopen_ty j X ty) T (Kopen_t (S j) X t')
    end.


  (* Local closure *)
  (* A locally closed term contains no unbound BVars. *)

  Inductive lcT : tname -> Prop :=
  | LCTName : forall X, lcT (FTName X).

  Inductive lcK : con -> Prop :=
  | LCKCon : forall X, lcK (FCon X).

  Definition lcd (d : data) : Prop :=
    Forall (fun '(T, Ks) => lcT T /\ Forall lcK Ks) d.

  Inductive lck : kind -> Prop :=
  | LCKType : lck KiType
  | LCKData : forall d, lcd d -> lck (KiData d)
  .

  Inductive lct : type -> Prop :=
  | LCTFVar : forall X, lct (TyFVar X)
  | LCTArr  : forall T1 T2, lct T1 -> lct T2 -> lct (TyArr T1 T2)
  | LCTAll  : forall L k T, lck k -> (forall X, X \notin L -> lct ({0 ~> TyFVar X}T)) -> lct (TyAll k T)
  | LCTCon  : forall ty T, lct ty -> lcT T -> lct (TyCon ty T)
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
  | LCCon    : forall K T t, lcK K ->  lct T -> lc t -> lc (TmCon K T t)
  | LCType   : forall L t, (forall X, X \notin L -> lc (Topen_t 0 (FTName X) t)) -> lc (TmType t)
  | LCConDef : forall L d ty T t, lcd d -> lct ty -> lcT T -> (forall X, X \notin L -> lc (Kopen_t 0 (FCon X) t)) -> lc (TmConDef d ty T t)
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
    | TyCon ty T => TyCon ({X => U}ty) T
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
    | TmCon K ty t' => TmCon K ({X => U}ty) ([{X => U}]t')
    | TmType t' => TmType ([{X => U}]t')
    | TmConDef d ty T t' => TmConDef d ({X => U}ty) T ([{X => U}]t')
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
    | TmCon K ty t' => TmCon K ty ([x => u]t')
    | TmType t' => TmType ([x => u]t')
    | TmConDef d ty T t' => TmConDef d ty T ([x => u]t')
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
  (* | BindMatch : match_assum -> binding *)
  .

  Definition env := env binding.

  Definition bsubst (X : var) (U : type) (b : binding) :=
    match b with
    | BindVar T => BindVar (tsubst X U T)
    | BindCon d ty T => BindCon d (tsubst X U ty) T
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
    let E := gather_vars_with (fun x : type => tfv x) in
    let F := gather_vars_with (fun x : kind => kfv x) in
    let G := gather_vars_with (fun x : data => dfv x) in
    let H := gather_vars_with (fun x : con => Kfv x) in
    let I := gather_vars_with (fun x : tname => Tfv x) in
    constr:(A \u B \u C \u D \u E \u F \u G \u H \u I).

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
    solve_eq T; inverts* Heq.
  Qed.

  Lemma topen_lct :
    forall K U T,
      lct T ->
      {K ~> U}T = T.
  Proof.
    introv Hlct. gen K.
    solve_eq Hlct.
    - pick_fresh x.
      rewrite topen_neq with (J := 0) (V := TyFVar x);
        auto.
  Qed.

  Lemma tsubst_topen_distr :
    forall X U k T1 T2,
      lct U ->
      {X => U} ({k ~> T2}T1) = {k ~> {X => U}T2} ({X => U}T1).
  Proof.
    introv Hlct. gen k.
    solve_eq T1. rewrite* topen_lct.
  Qed.

  Lemma tsubst_fresh :
    forall X T U,
      X \notin tfv T ->
      {X => U}T = T.
  Proof. introv Hfv ; solve_eq T. Qed.

  Lemma tsubst_intro :
    forall X T U,
      X \notin (tfv T) ->
      lct U ->
      {0 ~> U} T = {X => U}({0 ~> TyFVar X}T).
  Proof.
    introv Hfv Hlc.
    rewrite* tsubst_topen_distr.
    solve_var. rewrite* tsubst_fresh.
  Qed.

  Lemma tsubst_topen_comm :
    forall X Y U T n,
      X <> Y ->
      lct U ->
      {n ~> TyFVar Y} ({X => U}T) = {X => U} ({n ~> TyFVar Y} T).
  Proof.
    introv Hneq Hlct. gen n.
    solve_eq T ; rewrite* topen_lct.
  Qed.

  Lemma tsubst_lct :
    forall X U T,
      lct T ->
      lct U ->
      lct ({X => U}T).
  Proof.
    introv Hlct1 Hlct2.
    induction* Hlct1; solve_var.
    - apply_fresh* LCTAll.
      rewrite* tsubst_topen_comm.
  Qed.

  Lemma open_neq :
    forall i j u v t,
      i <> j ->
      [i ~> u]([j ~> v]t) = [j ~> v]t ->
      [i ~> u]t = t.
  Proof.
    introv Hneq Heq. gen i j. solve_eq t ; inverts* Heq.
  Qed.

  Lemma open_topen_neq :
    forall i u J V t,
      [i ~> u]([{J ~> V}]t) = [{J ~> V}] t ->
      [i ~> u]t = t.
  Proof.
    introv Heq. gen i J. solve_eq t ; inverts* Heq.
  Qed.

  Lemma open_Topen_rec :
    forall i u J V t,
      [i ~> u](Topen_t J V t) = Topen_t J V t ->
      [i ~> u]t = t.
  Proof.
    introv Heq. gen i J. solve_eq t ; inverts* Heq.
  Qed.

  Lemma open_Kopen_rec :
    forall i u J V t,
      [i ~> u](Kopen_t J V t) = Kopen_t J V t ->
      [i ~> u]t = t.
  Proof.
    introv Heq. gen i J. solve_eq t ; inverts* Heq.
  Qed.

  Lemma open_lc :
    forall k u t,
      lc t ->
      [k ~> u]t = t.
  Proof.
    introv Hlc. gen k.
    solve_eq Hlc.
    - pick_fresh x.
      rewrite open_neq with (j := 0) (v := TmFVar x);
        auto.
    - pick_fresh X.
      rewrite open_topen_neq with (J := 0) (V := TyFVar X);
        auto.
    - pick_fresh X.
      rewrite open_Topen_rec with (J := 0) (V := FTName X);
        auto.
    - pick_fresh X.
      rewrite open_Kopen_rec with (J := 0) (V := FCon X);
        auto.
  Qed.

  Lemma subst_open_distr :
    forall x u t1 t2,
      lc u ->
      [x => u] ([0 ~> t2] t1) = [0 ~> [x => u]t2]([x => u]t1).
  Proof.
    introv Hlc. generalize 0.
    solve_eq t1. rewrite* open_lc.
  Qed.

  Lemma subst_open_comm :
    forall x y u t,
      x <> y ->
      lc u ->
      [0 ~> TmFVar y]([x => u]t) = [x => u] ([0 ~> TmFVar y]t).
  Proof.
    introv Hneq Hlc. generalize 0.
    solve_eq t. apply* open_lc.
  Qed.

  Lemma subst_fresh :
    forall x t u,
      x \notin fv t ->
      [x => u]t = t.
  Proof. solve_eq t. Qed.

  Lemma subst_intro :
    forall x t u,
      x \notin (fv t) ->
      [0 ~> u] t = [x => u]([0 ~> TmFVar x]t).
  Proof.
    introv Hfv. unfolds.
    generalize 0. solve_eq t.
  Qed.

  Lemma tsubst_t_topen_distr :
    forall X U T t,
      lct U ->
      [{X => U}] ([{0 ~> T}] t) = [{0 ~> {X => U}T}] ([{X => U}]t).
  Proof.
    introv Hlct.
    generalize 0. solve_eq t ;
      apply* tsubst_topen_distr.
  Qed.

  Lemma tsubst_t_fresh :
    forall X t U,
      X \notin fv t ->
      [{X => U}]t = t.
  Proof.
    introv Hfv.
    solve_eq t; apply* tsubst_fresh.
  Qed.

  Lemma tsubst_t_intro :
    forall X U t,
      X \notin fv t ->
      lct U ->
      [{0 ~> U}]t = [{X => U}] ([{0 ~> TyFVar X}]t).
  Proof.
    introv Hftv Hlc.
    rewrite* tsubst_t_topen_distr.
    solve_var. rewrite* tsubst_t_fresh.
  Qed.

  Lemma topen_open_rec :
    forall n T t x,
      [{n ~> T}] ([0 ~> TmFVar x] t) = [0 ~> TmFVar x]t ->
      [{n ~> T}] t = t.
  Proof.
    introv Heq. generalize dependent 0. gen n.
    solve_eq t ; inverts* Heq.
  Qed.

  Lemma topen_t_neq :
    forall I J T U t,
      I <> J ->
      [{I ~> T}] ([{J ~> U}] t) = [{J ~> U}] t ->
      [{I ~> T}]t = t.
  Proof.
    introv Hneq Heq. gen I J.
    solve_eq t ; inverts* Heq; eauto using topen_neq.
  Qed.

  Lemma topen_Topen_rec :
    forall i j T U X,
      {i ~> T} (Topen_ty j (FTName X) U) = Topen_ty j (FTName X) U ->
      {i ~> T}U = U.
  Proof.
    introv Heq. gen i.
    solve_eq U ; inverts* Heq.
  Qed.

  Lemma topen_t_Topen_rec :
    forall n T t X,
      [{n ~> T}] (Topen_t 0 (FTName X) t) = Topen_t 0 (FTName X) t ->
      [{n ~> T}]t = t.
  Proof.
    introv Heq. generalize dependent 0. gen n.
    solve_eq t ; inverts* Heq ; apply* topen_Topen_rec.
  Qed.

  Lemma topen_Kopen_rec :
    forall i j T U X,
      {i ~> T} (Kopen_ty j (FCon X) U) = Kopen_ty j (FCon X) U ->
      {i ~> T}U = U.
  Proof.
    introv Heq. gen i.
    solve_eq U ; inverts* Heq.
  Qed.

  Lemma topen_t_Kopen_rec :
    forall n T t X,
      [{n ~> T}] (Kopen_t 0 (FCon X) t) = Kopen_t 0 (FCon X) t ->
      [{n ~> T}]t = t.
  Proof.
    introv Heq. generalize dependent 0. gen n.
    solve_eq t ; inverts* Heq ; apply* topen_Kopen_rec.
  Qed.

  Lemma topen_t_lc :
    forall T t n,
      lc t ->
      [{n ~> T}]t = t.
  Proof.
    introv Hlc. gen n.
    solve_eq Hlc ; try rewrite~ topen_lct.
    - pick_fresh_gen L x. apply* topen_open_rec.
    - pick_fresh_gen L x.
      rewrite* (@topen_t_neq (S n) 0 T (TyFVar x)).
    - pick_fresh_gen L x.
      apply* topen_t_Topen_rec.
    - pick_fresh_gen L x.
      apply* topen_t_Kopen_rec.
  Qed.

  Lemma topen_t_subst_comm :
    forall X x t1 t2,
      X \notin fv t2 ->
      lc t2 ->
      [{0 ~> TyFVar X}] ([x => t2]t1) = [x => t2]([{0 ~> TyFVar X}] t1).
  Proof.
    introv Hnin Hlc. generalize 0.
    solve_eq t1. rewrite* topen_t_lc.
  Qed.

  Lemma tsubst_t_open_comm :
    forall X x U t,
      [0 ~> TmFVar x] ([{X => U}]t) = [{X => U}] ([0 ~> TmFVar x]t).
  Proof. introv. generalize 0. solve_eq t. Qed.

  Lemma topen_notin :
    forall T X Y,
      X \notin tfv ({0 ~> TyFVar Y}T) ->
      X \notin tfv T.
  Proof.
    introv Hnin. generalize dependent 0.
    induction T; intros; simpls* ;
      apply notin_union_r in Hnin as (Hnin1 & Hnin2) ; eauto.
  Qed.

  Lemma topen_t_tsubst_comm :
    forall X Y T t,
      X <> Y ->
      lct T ->
      [{0 ~> TyFVar Y}] ([{X => T}]t) =
        [{X => T}]([{0 ~> TyFVar Y}] t).
  Proof.
    introv Hneq Hlct. generalize dependent 0.
    solve_eq t ; rewrite* tsubst_topen_comm.
  Qed.

End Syntax.
