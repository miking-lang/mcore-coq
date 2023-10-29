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

  Fixpoint tfv (T : type) :=
    match T with
    | TyBVar X => \{}
    | TyFVar X => \{X}
    | TyArr T1 T2 => tfv T1 \u tfv T2
    | TyAll k T' => tfv T'
    | TyCon ty T => tfv ty
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
    | TmCon K ty t' => tfv ty \u tfv_t t'
    | TmType t' => tfv_t t'
    | TmConDef d ty T t' => tfv ty \u tfv_t t'
    end.

  Fixpoint fv (t : term) :=
    match t with
    | TmBVar i => \{}
    | TmFVar x => \{x}
    | TmLam T t' => fv t'
    | TmApp t1 t2 => fv t1 \u fv t2
    | TmTyLam k t' => fv t'
    | TmTyApp t' T => fv t'
    | TmCon K ty t' => fv t'
    | TmType t' => fv t'
    | TmConDef d ty T t' => fv t'
    end.

  Notation Tfv T :=
    match T with
    | BTName X => \{}
    | FTName X => \{X}
    end.

  Definition Tfv_d (d : data) : vars :=
    fold_right (fun '(T, Ks) fvs => Tfv T \u fvs) \{} d.

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
    | TyCon ty T => Tfv_ty ty \u Tfv T
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
    | TmCon K ty t' => Tfv_ty ty \u Tfv_t t'
    | TmType t' => Tfv_t t'
    | TmConDef d ty T t' => Tfv_d d \u Tfv_ty ty \u Tfv T \u Tfv_t t'
    end.

  Notation Kfv K :=
    match K with
    | BCon X => \{}
    | FCon X => \{X}
    end.

  Definition Kfv_d (d : data) : vars :=
    fold_right (fun '(T, Ks) fvs =>
                  fold_right (fun K fvs => Kfv K \u fvs) \{} Ks
                             \u fvs)
               \{} d.

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
    | TyCon ty T => Kfv_ty ty
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
    | TmCon K ty t' => Kfv K \u Kfv_ty ty \u Kfv_t t'
    | TmType t' => Kfv_t t'
    | TmConDef d ty T t' => Kfv_d d \u Kfv_ty ty \u Kfv_t t'
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
    | TmConDef d ty T t' => TmConDef d ({S X ~> U}ty) T ([{X ~> U}]t')
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

  Notation lcT T := (exists T', T = FTName T').
  Notation lcK K := (exists K', K = FCon K').

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
  | LCTCon  : forall ty T, lct ty -> lct (TyCon ty (FTName T))
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
  | LCCon    : forall K T t, lct T -> lc t -> lc (TmCon (FCon K) T t)
  | LCType   : forall L t, (forall X, X \notin L -> lc (Topen_t 0 (FTName X) t)) -> lc (TmType t)
  | LCConDef : forall L d ty T t,
      lcd d ->
      (forall X, X \notin L -> lct ({0 ~> TyFVar X}ty)) ->
      (forall X, X \notin L -> lc (Kopen_t 0 (FCon X) t)) ->
      lc (TmConDef d ty (FTName T) t)
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
    | TyCon ty T => TyCon (Tsubst_ty X U ty) (Tsubst X U T)
    | TyData d => TyData (Tsubst_d X U d)
    end.

  Fixpoint Tsubst_t (X : var) (U : tname) (t : term) :=
    match t with
    | TmBVar i => t
    | TmFVar x => t
    | TmLam T t' => TmLam (Tsubst_ty X U T) (Tsubst_t X U t')
    | TmApp t1 t2 => TmApp (Tsubst_t X U t1) (Tsubst_t X U t2)
    | TmTyLam k t' => TmTyLam (Tsubst_k X U k) (Tsubst_t X U t')
    | TmTyApp t' T => TmTyApp (Tsubst_t X U t') (Tsubst_ty X U T)
    | TmCon K ty t' => TmCon K (Tsubst_ty X U ty) (Tsubst_t X U t')
    | TmType t' => TmType (Tsubst_t X U t')
    | TmConDef d ty T t' =>
        TmConDef (Tsubst_d X U d) (Tsubst_ty X U ty) (Tsubst X U T) (Tsubst_t X U t')
    end.


  Definition Ksubst (X : var) (U : con) (K : con) :=
    match K with
    | BCon _ => K
    | FCon Y => (If X = Y then U else K)
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
    | TyCon ty T => TyCon (Ksubst_ty X U ty) T
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
    | TmCon K ty t' => TmCon (Ksubst X U K) (Ksubst_ty X U ty) (Ksubst_t X U t')
    | TmType t' => TmType (Ksubst_t X U t')
    | TmConDef d ty T t' =>
        TmConDef (Ksubst_d X U d) (Ksubst_ty X U ty) T (Ksubst_t X U t')
    end.


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
    constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K \u L \u M \u N \u O \u P).

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
    forall X T U n,
      X \notin tfv T ->
      {n ~> U} T = {X => U}({n ~> TyFVar X}T).
  Proof. introv Hfv. gen n. solve_eq T. Qed.

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
    forall x u n t1 t2,
      lc u ->
      [x => u] ([n ~> t2] t1) = [n ~> [x => u]t2]([x => u]t1).
  Proof.
    introv Hlc. gen n.
    solve_eq t1. rewrite* open_lc.
  Qed.

  Lemma subst_open_comm :
    forall x y n u t,
      x <> y ->
      lc u ->
      [n ~> TmFVar y]([x => u]t) = [x => u] ([n ~> TmFVar y]t).
  Proof.
    introv Hneq Hlc. gen n.
    solve_eq t. apply* open_lc.
  Qed.

  Lemma subst_fresh :
    forall x t u,
      x \notin fv t ->
      [x => u]t = t.
  Proof. solve_eq t. Qed.

  Lemma subst_intro :
    forall x t u n,
      x \notin fv t ->
      [n ~> u] t = [x => u]([n ~> TmFVar x]t).
  Proof. introv Hfv. gen n. solve_eq t. Qed.

  Lemma tsubst_t_topen_distr :
    forall X U n T t,
      lct U ->
      [{X => U}] ([{n ~> T}] t) = [{n ~> {X => U}T}] ([{X => U}]t).
  Proof.
    introv Hlct.
    gen n. solve_eq t ;
      apply* tsubst_topen_distr.
  Qed.

  Lemma tsubst_t_fresh :
    forall X t U,
      X \notin tfv_t t ->
      [{X => U}]t = t.
  Proof.
    introv Hfv.
    solve_eq t; apply* tsubst_fresh.
  Qed.

  Lemma tsubst_t_intro :
    forall X U t,
      X \notin tfv_t t ->
      lct U ->
      [{0 ~> U}]t = [{X => U}] ([{0 ~> TyFVar X}]t).
  Proof.
    introv Hftv Hlc.
    rewrite* tsubst_t_topen_distr.
    solve_var. rewrite* tsubst_t_fresh.
  Qed.

  Lemma topen_open_rec :
    forall i j T t u,
      [{i ~> T}] ([j ~> u] t) = [j ~> u]t ->
      [{i ~> T}] t = t.
  Proof.
    introv Heq. gen i j.
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
    forall i j T U T',
      {i ~> T} (Topen_ty j T' U) = Topen_ty j T' U ->
      {i ~> T}U = U.
  Proof.
    introv Heq. gen i.
    solve_eq U ; inverts* Heq.
  Qed.

  Lemma topen_t_Topen_rec :
    forall i j T t T',
      [{i ~> T}] (Topen_t j T' t) = Topen_t j T' t ->
      [{i ~> T}]t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq ; apply* topen_Topen_rec.
  Qed.

  Lemma topen_Kopen_rec :
    forall i j T U K,
      {i ~> T} (Kopen_ty j K U) = Kopen_ty j K U ->
      {i ~> T}U = U.
  Proof.
    introv Heq. gen i.
    solve_eq U ; inverts* Heq.
  Qed.

  Lemma topen_t_Kopen_rec :
    forall i j T t K,
      [{i ~> T}] (Kopen_t j K t) = Kopen_t j K t ->
      [{i ~> T}]t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq ; apply* topen_Kopen_rec.
  Qed.

  Lemma topen_t_lc :
    forall X t n,
      lc t ->
      [{n ~> TyFVar X}]t = t.
  Proof.
    introv Hlc. gen n.
    solve_eq Hlc ; try solve [ rewrite~ topen_lct ] ; pick_fresh_gen L x.
    - apply* topen_open_rec.
    - apply* (topen_t_neq (S n) 0 (TyFVar X) (TyFVar x)).
    - apply* topen_t_Topen_rec.
    - apply topen_neq with (J := 0) (V := TyFVar x) ; auto.
      apply* topen_lct.
    - apply* topen_t_Kopen_rec.
  Qed.

  Lemma topen_t_subst_comm :
    forall X x n t1 t2,
      X \notin tfv_t t2 ->
      lc t2 ->
      [{n ~> TyFVar X}] ([x => t2]t1) = [x => t2]([{n ~> TyFVar X}] t1).
  Proof.
    introv Hnin Hlc. gen n.
    solve_eq t1. rewrite* topen_t_lc.
  Qed.

  Lemma tsubst_t_open_comm :
    forall X x n U t,
      [n ~> TmFVar x] ([{X => U}]t) = [{X => U}] ([n ~> TmFVar x]t).
  Proof. intros. gen n. solve_eq t. Qed.

  Lemma topen_notin :
    forall T X Y n,
      X \notin tfv ({n ~> TyFVar Y}T) ->
      X \notin tfv T.
  Proof.
    introv Hnin. gen n.
    induction T; intros; simpls* ;
      apply notin_union_r in Hnin as (Hnin1 & Hnin2) ; eauto.
  Qed.

  Lemma topen_t_tsubst_comm :
    forall X Y T n t,
      X <> Y ->
      lct T ->
      [{n ~> TyFVar Y}] ([{X => T}]t) =
        [{X => T}]([{n ~> TyFVar Y}] t).
  Proof.
    introv Hneq Hlct. gen n.
    solve_eq t ; rewrite* tsubst_topen_comm.
  Qed.

  Lemma Topen_Topen_neq :
    forall i j T T' T0,
      i <> j ->
      Topen i T (Topen j T' T0) = Topen j T' T0 ->
      Topen i T T0 = T0.
  Proof. introv Hneq Heq. solve_eq T0. Qed.

  Lemma Topen_d_lcd :
    forall j T d,
      lcd d ->
      Topen_d j T d = d.
  Proof.
    introv Hlcd.
    solve_eq Hlcd. unfolds Topen_d. rew_listx.
    destruct x. destruct H.
    inverts H. rewrite~ IHHlcd.
  Qed.

  Lemma Topen_Topen_d_neq :
    forall i j T T' d,
      i <> j ->
      Topen_d i T (Topen_d j T' d) = Topen_d j T' d ->
      Topen_d i T d = d.
  Proof.
    introv Hneq Heq. unfolds Topen_d.
    induction~ d.
    rew_listx in *. destruct a. inverts Heq.
    rewrite Topen_Topen_neq with (j := j) (T' := T') ; auto.
    rewrite~ IHd.
  Qed.

  Lemma Topen_Kopen_d_rec :
    forall i j T K d,
      Topen_d i T (Kopen_d j K d) = Kopen_d j K d ->
      Topen_d i T d = d.
  Proof.
    introv Heq. unfolds Topen_d. unfolds Kopen_d.
    induction~ d.
    rew_listx in *. destruct a. injection Heq ; intros. rewrite H0.
    rewrite~ IHd.
  Qed.

  Lemma Topen_k_lck :
    forall j T k,
      lck k ->
      Topen_k j T k = k.
  Proof.
    introv Hlck. solve_eq Hlck. rewrite~ Topen_d_lcd.
  Qed.

  Lemma Topen_Topen_k_neq :
    forall i j T T' k,
      i <> j ->
      Topen_k i T (Topen_k j T' k) = Topen_k j T' k ->
      Topen_k i T k = k.
  Proof.
    introv Hneq Heq.
    solve_eq k. inverts Heq. apply Topen_Topen_d_neq with (j := j) (T' := T') ; auto.
  Qed.

  Lemma Topen_Kopen_k_rec :
    forall i j T K k,
      Topen_k i T (Kopen_k j K k) = Kopen_k j K k ->
      Topen_k i T k = k.
  Proof.
    introv Heq. solve_eq k ; inverts Heq. apply* Topen_Kopen_d_rec.
  Qed.

  Lemma Topen_topen_rec :
    forall i j T U ty,
      Topen_ty i T ({j ~> U} ty) = {j ~> U}ty ->
      Topen_ty i T ty = ty.
  Proof.
    introv Heq. gen j.
    solve_eq ty ; inverts* Heq.
  Qed.

  Lemma Topen_ty_lct :
    forall k T ty,
      lct ty ->
      Topen_ty k T ty = ty.
  Proof.
    introv Hlct.
    solve_eq Hlct ;
      try solve [ apply* Topen_d_lcd
                | apply* Topen_k_lck ] ;
      pick_fresh_gen L x.
    - apply* Topen_topen_rec.
  Qed.

  Lemma Topen_Topen_ty_neq :
    forall i j T T' ty,
      i <> j ->
      Topen_ty i T (Topen_ty j T' ty) = Topen_ty j T' ty ->
      Topen_ty i T ty = ty.
  Proof.
    introv Hneq Heq. gen i j.
    solve_eq ty ; inverts* Heq.
    - apply Topen_Topen_k_neq with (j := j) (T' := T') ; auto.
    - apply Topen_Topen_neq with (j := j) (T' := T') ; auto.
    - apply Topen_Topen_d_neq with (j := j) (T' := T') ; auto.
  Qed.

  Lemma Topen_Kopen_ty_rec :
    forall i j T K ty,
      Topen_ty i T (Kopen_ty j K ty) = Kopen_ty j K ty ->
      Topen_ty i T ty = ty.
  Proof.
    introv Heq.
    solve_eq ty ; inverts* Heq.
    - apply* Topen_Kopen_k_rec.
    - apply* Topen_Kopen_d_rec.
  Qed.

  Lemma Topen_open_rec :
    forall i j T u t,
      Topen_t i T ([j ~> u] t) = [j ~> u]t ->
      Topen_t i T t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq.
  Qed.

  Lemma Topen_topen_t_rec :
    forall i j T ty t,
      Topen_t i T ([{j ~> ty}] t) = [{j ~> ty}] t ->
      Topen_t i T t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq ; apply* Topen_topen_rec.
  Qed.

  Lemma Topen_Topen_t_neq :
    forall i j T T' t,
      i <> j ->
      Topen_t i T (Topen_t j T' t) = Topen_t j T' t ->
      Topen_t i T t = t.
  Proof.
    introv Hneq Heq. gen i j.
    solve_eq t ; inverts* Heq ;
      solve [ apply Topen_Topen_neq with (j := j) (T' := T') ; auto
            | apply Topen_Topen_d_neq with (j := j) (T' := T') ; auto
            | apply Topen_Topen_k_neq with (j := j) (T' := T') ; auto
            | apply Topen_Topen_ty_neq with (j := j) (T' := T') ; auto ].
  Qed.

  Lemma Topen_Kopen_t_rec :
    forall i j T K t,
      Topen_t i T (Kopen_t j K t) = Kopen_t j K t ->
      Topen_t i T t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq ;
      solve [ apply* Topen_Kopen_d_rec
            | apply* Topen_Kopen_k_rec
            | apply* Topen_Kopen_ty_rec ].
  Qed.

  Lemma Topen_t_lc :
    forall k T t,
      lc t ->
      Topen_t k T t = t.
  Proof.
    introv Hlc. gen k.
    solve_eq Hlc ;
      try solve [ apply* Topen_d_lcd
                | apply* Topen_k_lck
                | apply* Topen_ty_lct ] ;
      pick_fresh_gen L x.
    - apply* Topen_open_rec.
    - apply* Topen_topen_t_rec.
    - apply* (Topen_Topen_t_neq (S k) 0 T (FTName x)).
    - apply* Topen_topen_rec.
      apply* Topen_ty_lct.
    - apply* Topen_Kopen_t_rec.
  Qed.

  Lemma Topen_t_subst_comm :
    forall x n T t1 t2,
      lc t2 ->
      Topen_t n T ([x => t2]t1) = [x => t2] (Topen_t n T t1).
  Proof.
    introv Hlc. gen n. solve_eq t1. apply* Topen_t_lc.
  Qed.

  Lemma Topen_tsubst_comm :
    forall X n T U ty,
      lct U ->
      Topen_ty n T ({X => U}ty) = {X => U} (Topen_ty n T ty).
  Proof.
    introv Hlct. gen n. solve_eq ty ; apply* Topen_ty_lct.
  Qed.

  Lemma Topen_t_tsubst_comm :
    forall X n T U t,
      lct U ->
      Topen_t n T ([{X => U}]t) = [{X => U}] (Topen_t n T t).
  Proof.
    introv Hlc. gen n. solve_eq t ; apply* Topen_tsubst_comm.
  Qed.


  Lemma Kopen_Kopen_neq :
    forall i j K K' K0,
      i <> j ->
      Kopen i K (Kopen j K' K0) = Kopen j K' K0 ->
      Kopen i K K0 = K0.
  Proof. introv Hneq Heq. solve_eq K0. Qed.

  Lemma Kopen_d_lcd :
    forall j T d,
      lcd d ->
      Kopen_d j T d = d.
  Proof.
    introv Hlcd.
    solve_eq Hlcd. unfolds Kopen_d. rew_listx.
    destruct x. destruct H. rewrite~ IHHlcd.
    induction~ l0. rew_listx in *. destruct H0. inverts H0. simpls.
    apply IHl0 in H1. injection H1 ; intros. rewrite* H0.
  Qed.

  Lemma Kopen_Kopen_d_neq :
    forall i j K K' d,
      i <> j ->
      Kopen_d i K (Kopen_d j K' d) = Kopen_d j K' d ->
      Kopen_d i K d = d.
  Proof.
    introv Hneq Heq. unfolds Kopen_d.
    induction~ d.
    rew_listx in *. destruct a. inverts Heq.
    rewrite~ IHd. repeat fequals.
    induction~ l. rew_listx in *. inverts H0. rewrite~ IHl.
    rewrite Kopen_Kopen_neq with (j := j) (K' := K') ; auto.
  Qed.

  Lemma Kopen_Topen_d_rec :
    forall i j T K d,
      Kopen_d i K (Topen_d j T d) = Topen_d j T d ->
      Kopen_d i K d = d.
  Proof.
    introv Heq. unfolds Kopen_d. unfolds Topen_d.
    induction~ d.
    rew_listx in *. destruct a. injection Heq ; intros. rewrite H0.
    rewrite~ IHd.
  Qed.

  Lemma Kopen_k_lck :
    forall j T k,
      lck k ->
      Kopen_k j T k = k.
  Proof.
    introv Hlck. solve_eq Hlck. rewrite~ Kopen_d_lcd.
  Qed.

  Lemma Kopen_Kopen_k_neq :
    forall i j K K' k,
      i <> j ->
      Kopen_k i K (Kopen_k j K' k) = Kopen_k j K' k ->
      Kopen_k i K k = k.
  Proof.
    introv Hneq Heq.
    solve_eq k. inverts Heq. apply Kopen_Kopen_d_neq with (j := j) (K' := K') ; auto.
  Qed.

  Lemma Kopen_Topen_k_rec :
    forall i j T K k,
      Kopen_k i K (Topen_k j T k) = Topen_k j T k ->
      Kopen_k i K k = k.
  Proof.
    introv Heq. solve_eq k ; inverts Heq. apply* Kopen_Topen_d_rec.
  Qed.

  Lemma Kopen_topen_rec :
    forall i j T U ty,
      Kopen_ty i T ({j ~> U} ty) = {j ~> U}ty ->
      Kopen_ty i T ty = ty.
  Proof.
    introv Heq. gen j.
    solve_eq ty ; inverts* Heq.
  Qed.

  Lemma Kopen_ty_lct :
    forall k T ty,
      lct ty ->
      Kopen_ty k T ty = ty.
  Proof.
    introv Hlct.
    solve_eq Hlct ;
      try solve [ apply* Kopen_d_lcd
                | apply* Kopen_k_lck ] ;
      pick_fresh_gen L x.
    - apply* Kopen_topen_rec.
  Qed.

  Lemma Kopen_Kopen_ty_neq :
    forall i j K K' ty,
      i <> j ->
      Kopen_ty i K (Kopen_ty j K' ty) = Kopen_ty j K' ty ->
      Kopen_ty i K ty = ty.
  Proof.
    introv Hneq Heq. gen i j.
    solve_eq ty ; inverts* Heq.
    - apply Kopen_Kopen_k_neq with (j := j) (K' := K') ; auto.
    - apply Kopen_Kopen_d_neq with (j := j) (K' := K') ; auto.
  Qed.

  Lemma Kopen_Topen_ty_rec :
    forall i j T K ty,
      Kopen_ty i K (Topen_ty j T ty) = Topen_ty j T ty ->
      Kopen_ty i K ty = ty.
  Proof.
    introv Heq.
    solve_eq ty ; inverts* Heq.
    - apply* Kopen_Topen_k_rec.
    - apply* Kopen_Topen_d_rec.
  Qed.

  Lemma Kopen_open_rec :
    forall i j T u t,
      Kopen_t i T ([j ~> u] t) = [j ~> u]t ->
      Kopen_t i T t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq.
  Qed.

  Lemma Kopen_topen_t_rec :
    forall i j T ty t,
      Kopen_t i T ([{j ~> ty}] t) = [{j ~> ty}] t ->
      Kopen_t i T t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq ; apply* Kopen_topen_rec.
  Qed.

  Lemma Kopen_Kopen_t_neq :
    forall i j K K' t,
      i <> j ->
      Kopen_t i K (Kopen_t j K' t) = Kopen_t j K' t ->
      Kopen_t i K t = t.
  Proof.
    introv Hneq Heq. gen i j.
    solve_eq t ; inverts* Heq ;
      try solve [ apply Kopen_Kopen_neq with (j := j) (K' := K') ; auto
                | apply Kopen_Kopen_d_neq with (j := j) (K' := K') ; auto
                | apply Kopen_Kopen_k_neq with (j := j) (K' := K') ; auto
                | apply Kopen_Kopen_ty_neq with (j := j) (K' := K') ; auto ].
  Qed.

  Lemma Kopen_Topen_t_rec :
    forall i j T K t,
      Kopen_t i K (Topen_t j T t) = Topen_t j T t ->
      Kopen_t i K t = t.
  Proof.
    introv Heq. gen i j.
    solve_eq t ; inverts* Heq ;
      solve [ apply* Kopen_Topen_d_rec
            | apply* Kopen_Topen_k_rec
            | apply* Kopen_Topen_ty_rec ].
  Qed.

  Lemma Kopen_t_lc :
    forall k K t,
      lc t ->
      Kopen_t k K t = t.
  Proof.
    introv Hlc. gen k.
    solve_eq Hlc ;
      try solve [ apply* Kopen_d_lcd
                | apply* Kopen_k_lck
                | apply* Kopen_ty_lct ] ;
      pick_fresh_gen L x.
    - apply* Kopen_open_rec.
    - apply* Kopen_topen_t_rec.
    - apply* Kopen_Topen_t_rec.
    - apply* Kopen_topen_rec.
      apply* Kopen_ty_lct.
    - apply* (Kopen_Kopen_t_neq (S k) 0 K (FCon x)).
  Qed.

  Lemma Kopen_t_subst_comm :
    forall x n K t1 t2,
      lc t2 ->
      Kopen_t n K ([x => t2]t1) = [x => t2] (Kopen_t n K t1).
  Proof.
    introv Hlc. gen n. solve_eq t1 ; apply* Kopen_t_lc.
  Qed.

  Lemma Kopen_tsubst_comm :
    forall X n T U ty,
      lct U ->
      Kopen_ty n T ({X => U}ty) = {X => U} (Kopen_ty n T ty).
  Proof.
    introv Hlct. gen n. solve_eq ty ; apply* Kopen_ty_lct.
  Qed.

  Lemma Kopen_t_tsubst_comm :
    forall X n T U t,
      lct U ->
      Kopen_t n T ([{X => U}]t) = [{X => U}] (Kopen_t n T t).
  Proof.
    introv Hlc. gen n. solve_eq t ; apply* Kopen_tsubst_comm.
  Qed.

  (* Lemma Topen_t_open_comm : *)
  (*   forall i n T v t, *)
  (*     lc v -> *)
  (*     Topen_t i T ([n ~> v] t) = [n ~> v] (Topen_t i T t). *)
  (* Proof. *)
  (*   introv Hlc. gen n i. solve_eq t. apply* Topen_t_lc. *)
  (* Qed. *)

  (* Lemma Topen_ty_topen_comm : *)
  (*   forall i n T ty1 ty2, *)
  (*     lct ty1 -> *)
  (*     Topen_ty i T ({n ~> ty1} ty2) = {n ~> ty1} (Topen_ty i T ty2). *)
  (* Proof. *)
  (*   introv. gen n. solve_eq ty2. apply* Topen_ty_lct. *)
  (* Qed. *)

  (* Lemma Topen_t_topen_comm : *)
  (*   forall i n T ty t, *)
  (*     lct ty -> *)
  (*     Topen_t i T ([{n ~> ty}] t) = [{n ~> ty}] (Topen_t i T t). *)
  (* Proof. *)
  (*   introv. gen n i. solve_eq t ; apply* Topen_ty_topen_comm. *)
  (* Qed. *)

  Lemma Topen_t_close :
    forall i T t,
      lc t ->
      exists t', t = Topen_t i (FTName T) t' /\ T \notin Tfv_t t'.
  Proof.
    (* introv Hlc. gen i. induction t ; intros ; inverts Hlc. *)
    (* - exists (TmFVar v). splits ; simpls~. *)
    (* - exists (TmLam t t') *)
  Admitted.

  Lemma Kopen_t_close :
    forall i K t,
      lc t ->
      exists t', t = Kopen_t i (FCon K) t' /\ K \notin Kfv_t t'.
  Proof. Admitted.

  Lemma Tsubst_t_open_distr :
    forall i X T t u,
      Tsubst_t X T ([i ~> u] t) =
        [i ~> Tsubst_t X T u] (Tsubst_t X T t).
  Proof. introv. gen i. solve_eq t. Qed.

  Lemma Tsubst_ty_topen_distr :
    forall i X T ty U,
      Tsubst_ty X T ({i ~> U} ty) =
        {i ~> Tsubst_ty X T U} (Tsubst_ty X T ty).
  Proof. introv. gen i. solve_eq ty. Qed.

  Lemma Tsubst_t_topen_distr :
    forall i X T t U,
      Tsubst_t X T ([{i ~> U}] t) =
        [{i ~> Tsubst_ty X T U}] (Tsubst_t X T t).
  Proof. introv. gen i. solve_eq t ; apply Tsubst_ty_topen_distr. Qed.

  Lemma Tsubst_d_Topen_comm :
    forall i X T U d,
      X <> T ->
      Topen_d i (FTName T) (Tsubst_d X (FTName U) d) =
        Tsubst_d X (FTName U) (Topen_d i (FTName T) d).
  Proof.
    introv Hneq. unfolds Topen_d. unfolds Tsubst_d.
    induction~ d.
    rew_listx in *. destruct a. rewrite~ IHd. destruct t ; solve_var.
  Qed.

  Lemma Tsubst_k_Topen_comm :
    forall i X T U k,
      X <> T ->
      Topen_k i (FTName T) (Tsubst_k X (FTName U) k) =
        Tsubst_k X (FTName U) (Topen_k i (FTName T) k).
  Proof.
    introv Hneq. solve_eq k. apply~ Tsubst_d_Topen_comm.
  Qed.

  Lemma Tsubst_ty_Topen_comm :
    forall i X T U ty,
      X <> T ->
      Topen_ty i (FTName T) (Tsubst_ty X (FTName U) ty) =
        Tsubst_ty X (FTName U) (Topen_ty i (FTName T) ty).
  Proof.
    introv Hneq. solve_eq ty.
    - apply~ Tsubst_k_Topen_comm.
    - destruct t ; solve_var.
    - apply~ Tsubst_d_Topen_comm.
  Qed.

  Lemma Tsubst_t_Topen_comm :
    forall i X T U t,
      X <> T ->
      Topen_t i (FTName T) (Tsubst_t X (FTName U) t) =
        Tsubst_t X (FTName U) (Topen_t i (FTName T) t).
  Proof.
    introv Hneq. gen i. solve_eq t ;
      try solve [ apply~ Tsubst_d_Topen_comm
                | apply~ Tsubst_k_Topen_comm
                | apply~ Tsubst_ty_Topen_comm ].
    destruct t0 ; solve_var.
  Qed.

  Lemma Tsubst_d_Kopen_comm :
    forall i X K U d,
      Kopen_d i (FCon K) (Tsubst_d X (FTName U) d) =
        Tsubst_d X (FTName U) (Kopen_d i (FCon K) d).
  Proof.
    intros. unfolds Kopen_d. unfolds Tsubst_d.
    induction~ d.
    rew_listx in *. destruct a. rewrite~ IHd.
  Qed.

  Lemma Tsubst_k_Kopen_comm :
    forall i X K U k,
      Kopen_k i (FCon K) (Tsubst_k X (FTName U) k) =
        Tsubst_k X (FTName U) (Kopen_k i (FCon K) k).
  Proof. intros. solve_eq k. apply~ Tsubst_d_Kopen_comm. Qed.

  Lemma Tsubst_ty_Kopen_comm :
    forall i X K U ty,
      Kopen_ty i (FCon K) (Tsubst_ty X (FTName U) ty) =
        Tsubst_ty X (FTName U) (Kopen_ty i (FCon K) ty).
  Proof.
    intros. solve_eq ty.
    - apply~ Tsubst_k_Kopen_comm.
    - apply~ Tsubst_d_Kopen_comm.
  Qed.

  Lemma Tsubst_t_Kopen_comm :
    forall i X K U t,
      Kopen_t i (FCon K) (Tsubst_t X (FTName U) t) =
        Tsubst_t X (FTName U) (Kopen_t i (FCon K) t).
  Proof.
    introv. gen i. solve_eq t ;
      try solve [ apply~ Tsubst_d_Kopen_comm
                | apply~ Tsubst_k_Kopen_comm
                | apply~ Tsubst_ty_Kopen_comm ].
  Qed.

  Lemma Tsubst_d_intro :
    forall X U i d,
      X \notin Tfv_d d ->
      Topen_d i U d = Tsubst_d X U (Topen_d i (FTName X) d).
  Proof.
    introv Hfv. unfolds Topen_d. unfolds Tsubst_d. unfolds Tfv_d.
    induction~ d.
    rew_listx in *. destruct a. rewrite~ IHd. destruct t ; solve_var.
  Qed.

  Lemma Tsubst_k_intro :
    forall X U i k,
      X \notin Tfv_k k ->
      Topen_k i U k = Tsubst_k X U (Topen_k i (FTName X) k).
  Proof. introv Hfv. solve_eq k. apply~ Tsubst_d_intro. Qed.

  Lemma Tsubst_ty_intro :
    forall X U i ty,
      X \notin Tfv_ty ty ->
      Topen_ty i U ty = Tsubst_ty X U (Topen_ty i (FTName X) ty).
  Proof.
    introv Hfv. solve_eq ty.
    - apply~ Tsubst_k_intro.
    - destruct t ; solve_var.
    - apply~ Tsubst_d_intro.
  Qed.

  Lemma Tsubst_t_intro :
    forall X U i t,
      X \notin Tfv_t t ->
      Topen_t i U t = Tsubst_t X U (Topen_t i (FTName X) t).
  Proof.
    introv Hfv. gen i. solve_eq t ;
      try solve [ apply~ Tsubst_d_intro
                | apply~ Tsubst_k_intro
                | apply~ Tsubst_ty_intro ].
    destruct t0 ; solve_var.
  Qed.

  Lemma Ksubst_t_open_distr :
    forall i X K t u,
      Ksubst_t X K ([i ~> u] t) =
        [i ~> Ksubst_t X K u] (Ksubst_t X K t).
  Proof. introv. gen i. solve_eq t. Qed.

  Lemma Ksubst_ty_topen_distr :
    forall i X K ty U,
      Ksubst_ty X K ({i ~> U} ty) =
        {i ~> Ksubst_ty X K U} (Ksubst_ty X K ty).
  Proof. introv. gen i. solve_eq ty. Qed.

  Lemma Ksubst_t_topen_distr :
    forall i X K t U,
      Ksubst_t X K ([{i ~> U}] t) =
        [{i ~> Ksubst_ty X K U}] (Ksubst_t X K t).
  Proof. introv. gen i. solve_eq t ; apply Ksubst_ty_topen_distr. Qed.

  Lemma Ksubst_d_Kopen_comm :
    forall i X K U d,
      X <> K ->
      Kopen_d i (FCon K) (Ksubst_d X (FCon U) d) =
        Ksubst_d X (FCon U) (Kopen_d i (FCon K) d).
  Proof.
    introv Hneq. unfolds Kopen_d. unfolds Ksubst_d.
    induction~ d. rew_listx. destruct a. rewrite~ IHd.
    induction~ l. rew_listx. inverts IHl. rewrite H0. destruct a ; solve_var.
  Qed.

  Lemma Ksubst_k_Kopen_comm :
    forall i X K U k,
      X <> K ->
      Kopen_k i (FCon K) (Ksubst_k X (FCon U) k) =
        Ksubst_k X (FCon U) (Kopen_k i (FCon K) k).
  Proof.
    introv Hneq. solve_eq k. apply~ Ksubst_d_Kopen_comm.
  Qed.

  Lemma Ksubst_ty_Kopen_comm :
    forall i X K U ty,
      X <> K ->
      Kopen_ty i (FCon K) (Ksubst_ty X (FCon U) ty) =
        Ksubst_ty X (FCon U) (Kopen_ty i (FCon K) ty).
  Proof.
    introv Hneq. solve_eq ty.
    - apply~ Ksubst_k_Kopen_comm.
    - apply~ Ksubst_d_Kopen_comm.
  Qed.

  Lemma Ksubst_t_Kopen_comm :
    forall i X K U t,
      X <> K ->
      Kopen_t i (FCon K) (Ksubst_t X (FCon U) t) =
        Ksubst_t X (FCon U) (Kopen_t i (FCon K) t).
  Proof.
    introv Hneq. gen i. solve_eq t ;
      try solve [ apply~ Ksubst_d_Kopen_comm
                | apply~ Ksubst_k_Kopen_comm
                | apply~ Ksubst_ty_Kopen_comm ].
    destruct c ; solve_var.
  Qed.

  Lemma Ksubst_d_Topen_comm :
    forall i X T U d,
      Topen_d i (FTName T) (Ksubst_d X (FCon U) d) =
        Ksubst_d X (FCon U) (Topen_d i (FTName T) d).
  Proof.
    intros. unfolds Topen_d. unfolds Ksubst_d.
    induction~ d.
    rew_listx in *. destruct a. rewrite~ IHd.
  Qed.

  Lemma Ksubst_k_Topen_comm :
    forall i X T U k,
      Topen_k i (FTName T) (Ksubst_k X (FCon U) k) =
        Ksubst_k X (FCon U) (Topen_k i (FTName T) k).
  Proof. intros. solve_eq k. apply~ Ksubst_d_Topen_comm. Qed.

  Lemma Ksubst_ty_Topen_comm :
    forall i X T U ty,
      Topen_ty i (FTName T) (Ksubst_ty X (FCon U) ty) =
        Ksubst_ty X (FCon U) (Topen_ty i (FTName T) ty).
  Proof.
    intros. solve_eq ty.
    - apply~ Ksubst_k_Topen_comm.
    - apply~ Ksubst_d_Topen_comm.
  Qed.

  Lemma Ksubst_t_Topen_comm :
    forall i X T U t,
      Topen_t i (FTName T) (Ksubst_t X (FCon U) t) =
        Ksubst_t X (FCon U) (Topen_t i (FTName T) t).
  Proof.
    introv. gen i. solve_eq t ;
      try solve [ apply~ Ksubst_d_Topen_comm
                | apply~ Ksubst_k_Topen_comm
                | apply~ Ksubst_ty_Topen_comm ].
  Qed.

  Lemma Ksubst_d_intro :
    forall X U i d,
      X \notin Kfv_d d ->
      Kopen_d i U d = Ksubst_d X U (Kopen_d i (FCon X) d).
  Proof.
    introv Hfv. unfolds Kopen_d. unfolds Ksubst_d. unfolds Kfv_d.
    induction~ d. rew_listx in *. destruct a. rewrite~ IHd.
    induction~ l. rew_listx in Hfv. rew_listx.
    forwards~ IHl': IHl. inverts IHl'.
    rewrite H0. destruct a ; solve_var.
  Qed.

  Lemma Ksubst_k_intro :
    forall X U i k,
      X \notin Kfv_k k ->
      Kopen_k i U k = Ksubst_k X U (Kopen_k i (FCon X) k).
  Proof. introv Hfv. solve_eq k. apply~ Ksubst_d_intro. Qed.

  Lemma Ksubst_ty_intro :
    forall X U i ty,
      X \notin Kfv_ty ty ->
      Kopen_ty i U ty = Ksubst_ty X U (Kopen_ty i (FCon X) ty).
  Proof.
    introv Hfv. solve_eq ty.
    - apply~ Ksubst_k_intro.
    - apply~ Ksubst_d_intro.
  Qed.

  Lemma Ksubst_t_intro :
    forall X U i t,
      X \notin Kfv_t t ->
      Kopen_t i U t = Ksubst_t X U (Kopen_t i (FCon X) t).
  Proof.
    introv Hfv. gen i. solve_eq t ;
      try solve [ apply~ Ksubst_d_intro
                | apply~ Ksubst_k_intro
                | apply~ Ksubst_ty_intro ].
    destruct c ; solve_var.
  Qed.

End Syntax.
