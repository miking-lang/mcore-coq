From TLC Require Import LibList LibLN.
From MCore Require Import Syntax SyntaxProps.
Import LibList.LibListNotation.

Notation mem := LibList.mem.

(*********************************)
(** TYPING RELATION DEFINITIONS **)
(*********************************)

Module Typing (P : PAT).
  Module SP := SyntaxProps P.
  Export SP.

  Module Type PATCHECK.
    Parameter ok_pat : env -> pat -> type -> type -> Prop.
    Parameter matches_contradictory : env -> Prop.
    Parameter pats_compatible : list pat -> Prop.
    Parameter pats_exhaustive : env -> list pat -> type -> Prop.
  End PATCHECK.

  Module Typing1 (PC : PATCHECK).
    Export PC.

    Inductive ok_cons : env -> list con -> tname -> Prop :=
    | CNil  : forall Gamma T, ok_cons Gamma nil T
    | CCons : forall Gamma K Ks d ty T,
        ok_cons Gamma Ks T ->
        ~ mem (FCon K) Ks ->
        binds K (BindCon d ty T) Gamma ->
        ok_cons Gamma (FCon K :: Ks) T.
    #[export]
     Hint Constructors ok_cons : mcore.

    Inductive ok_data : env -> data -> Prop :=
    | DNil  : forall Gamma, ok_data Gamma nil
    | DCons :
      forall Gamma d T Ks,
        ok_data Gamma d ->
        (forall Ks, ~ mem (FTName T, Ks) d) ->
        binds T BindTName Gamma ->
        ok_cons Gamma Ks (FTName T) ->
        ok_data Gamma ((FTName T , Ks) :: d).
    #[export]
     Hint Constructors ok_data : mcore.

    Definition data_sub (d2 : data) (d1 : data) :=
      forall T Ks, mem (T, Ks) d2 ->
              exists Ks', mem (T, Ks') d1 /\ forall K, mem K Ks -> mem K Ks'.

    Inductive ok_kind : env -> kind -> Prop :=
    | TypeOk : forall Gamma,
        ok_kind Gamma KiType
    | DataOk : forall Gamma d,
        ok_data Gamma d ->
        ok_kind Gamma (KiData d).
    #[export]
     Hint Constructors ok_kind : mcore.

    Reserved Notation "Gamma |= T ~:: k " (at level 50).
    Inductive ok_type : env -> type -> kind -> Prop :=
    | KVar : forall Gamma tv k,
        ok_env Gamma ->
        binds tv (BindTVar k) Gamma ->
        Gamma |= TyFVar tv ~:: k
    | KArr : forall Gamma ty1 ty2,
        Gamma |= ty1 ~:: KiType ->
        Gamma |= ty2 ~:: KiType ->
        Gamma |= TyArr ty1 ty2 ~:: KiType
    | KAll : forall L Gamma k ty,
        ok_kind Gamma k ->
        (forall X, X \notin L ->
                   (Gamma & X ~ BindTVar k) |= {0 ~> TyFVar X} ty ~:: KiType) ->
        Gamma |= TyAll k ty ~:: KiType
    | KProd : forall Gamma ty1 ty2,
        Gamma |= ty1 ~:: KiType ->
        Gamma |= ty2 ~:: KiType ->
        Gamma |= TyProd ty1 ty2 ~:: KiType
    | KCon : forall Gamma ty d T Ks,
        Gamma |= ty ~:: KiData d ->
        mem (FTName T, Ks) d ->
        Gamma |= TyCon ty (FTName T) ~:: KiType
    | KSem : forall Gamma ty1 ty2 ps,
        Gamma |= ty1 ~:: KiType ->
        Gamma |= ty2 ~:: KiType ->
        Forall (fun p => exists ty1', ok_pat Gamma p ty1 ty1') ps ->
        Gamma |= TySem ty1 ty2 ps ~:: KiType
    | KData : forall Gamma d,
        ok_env Gamma ->
        ok_data Gamma d ->
        Gamma |= TyData d ~:: KiData d
    | KDataSub : forall Gamma ty d1 d2,
        Gamma |= ty ~:: KiData d1 ->
        data_sub d2 d1 ->
        ok_data Gamma d2 ->
        Gamma |= ty ~:: KiData d2
    where " Gamma |= T ~:: k " := (ok_type Gamma T k)

    with ok_env : env -> Prop :=
    | EnvEmpty : ok_env empty
    | EnvTName : forall Gamma X, ok_env Gamma -> X # Gamma -> ok_env (Gamma & X ~ BindTName)
    | EnvCon   :
      forall L Gamma K d ty T,
        ok_env Gamma ->
        K # Gamma ->
        ok_data Gamma d ->
        (forall X, X \notin L -> Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty ~:: KiType) ->
        binds T BindTName Gamma ->
        ok_env (Gamma & K ~ BindCon d ty (FTName T))
    | EnvTVar : forall Gamma X k,
        ok_env Gamma ->
        X # Gamma ->
        ok_kind Gamma k ->
        ok_env (Gamma & X ~ BindTVar k)
    | EnvVar : forall Gamma x ty,
        ok_env Gamma ->
        x # Gamma ->
        Gamma |= ty ~:: KiType ->
        ok_env (Gamma & x ~ BindVar ty)
    (* | EnvMatch : forall Gamma M m, *)
    (*     ok_env Gamma -> *)
    (*     M # Gamma -> *)
    (*     ok_env (Gamma & M ~ BindMatch m) *)
    .
    #[export]
     Hint Constructors ok_type : mcore.
    #[export]
     Hint Constructors ok_env : mcore.

    Reserved Notation "Gamma |= t ~: T " (at level 50).
    Inductive ok_term : env -> term -> type -> Prop :=
    | TVar : forall Gamma x ty,
        ok_env Gamma ->
        binds x (BindVar ty) Gamma ->
        Gamma |= TmFVar x ~: ty
    | TLam : forall L Gamma ty1 ty2 t,
        Gamma |= ty1 ~:: KiType ->
        (forall x, x \notin L ->
              (Gamma & x ~ BindVar ty1) |= [0 ~> TmFVar x]t ~: ty2) ->
        Gamma |= TmLam ty1 t ~: TyArr ty1 ty2
    | TApp : forall Gamma ty1 ty2 t1 t2,
        Gamma |= t1 ~: TyArr ty1 ty2 ->
        Gamma |= t2 ~: ty1 ->
        Gamma |= TmApp t1 t2 ~: ty2
    | TTyLam : forall L Gamma k ty t,
        ok_kind Gamma k ->
        (forall X, X \notin L ->
              (Gamma & X ~ BindTVar k) |= [{0 ~> TyFVar X}]t ~: ({0 ~> TyFVar X}ty)) ->
        Gamma |= TmTyLam k t ~: (TyAll k ty)
    | TTyApp : forall Gamma k ty1 ty2 t,
        Gamma |= t ~: TyAll k ty1 ->
        Gamma |= ty2 ~:: k ->
        Gamma |= TmTyApp t ty2 ~: ({0 ~> ty2}ty1)
    | TFix : forall Gamma ty t,
        Gamma |= t ~: TyArr ty ty ->
        Gamma |= TmFix t ~: ty
    | TProd : forall Gamma ty1 ty2 t1 t2,
        Gamma |= t1 ~: ty1 ->
        Gamma |= t2 ~: ty2 ->
        Gamma |= TmProd t1 t2 ~: TyProd ty1 ty2
    | TProj1 : forall Gamma ty1 ty2 t,
        Gamma |= t ~: TyProd ty1 ty2 ->
        Gamma |= TmProj F1 t ~: ty1
    | TProj2 : forall Gamma ty1 ty2 t,
        Gamma |= t ~: TyProd ty1 ty2 ->
        Gamma |= TmProj F2 t ~: ty2
    | TCon : forall Gamma K d ty1 ty2 T t,
        binds K (BindCon d ty1 (FTName T)) Gamma ->
        Gamma |= ty2 ~:: KiData d ->
        Gamma |= ty2 ~:: KiData [ (FTName T , FCon K :: []) ] ->
        Gamma |= t ~: ({0 ~> ty2}ty1) ->
        Gamma |= TmCon (FCon K) ty2 t ~: TyCon ty2 (FTName T)
    (* | TmMatch' : forall {Gamma : env} {vs : var_env} {t t1 t2 : term} *)
    (*                     {ty1 ty2 : type} {p : pat}, *)
    (*     ok_term Gamma t ty1 -> *)
    (*     ok_pat  Gamma p ty1 vs -> *)
    (*     ok_term (Gamma <| vars ::= fun vs' => vs ++ vs' |> <| matches ::= fun ms => Match t p :: ms |> *)
    (*             t1 ty2 -> *)
    (*     ok_term (Gamma <| matches ::= fun ms => NoMatch t p :: ms |>) *)
    (*             t2 ty2 -> *)
    (*     ok_term Gamma (TmMatch t p t1 t2) ty2 *)
    (* | TmNever' : forall {Gamma : env} {ty : type}, *)
    (*     matches_contradictory Gamma.(matches) -> *)
    (*     ok_term Gamma TmNever ty *)
    | TType : forall L Gamma t ty,
        (forall T, T \notin L ->
              Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty) ->
        Gamma |= TmType t ~: ty
    | TConDef : forall L Gamma d ty1 ty2 T t,
        ok_data Gamma d ->
        (forall X, X \notin L ->
              Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty1 ~:: KiType) ->
        binds T BindTName Gamma ->
        (forall K, K \notin L ->
              Gamma & K ~ BindCon d ty1 (FTName T) |= Kopen_t 0 (FCon K) t ~: ty2) ->
        Gamma |= TmConDef d ty1 (FTName T) t ~: ty2
    | TSem : forall L Gamma ty1 ty1' ty2 p t,
        Gamma |= ty1 ~:: KiType ->
        ok_pat Gamma p ty1 ty1' ->
        (forall x, x \notin L ->
              Gamma & x ~ BindVar ty1' |= [0 ~> TmFVar x]t ~: ty2) ->
        Gamma |= TmSem ty1 p t ~: TySem ty1 ty2 [ p ]
    | TComp : forall Gamma ty1 ty2 t1 t2 ps1 ps2,
        Gamma |= t1 ~: TySem ty1 ty2 ps1 ->
        Gamma |= t2 ~: TySem ty1 ty2 ps2 ->
        pats_compatible (ps1 ++ ps2) ->
        Gamma |= TmComp t1 t2 ~: TySem ty1 ty2 (ps1 ++ ps2)
    | TSemApp : forall Gamma ty1 ty2 t1 t2 ps,
        Gamma |= t1 ~: TySem ty1 ty2 ps ->
        Gamma |= t2 ~: ty1 ->
        pats_exhaustive Gamma ps ty1 ->
        Gamma |= TmSemApp t1 t2 ~: ty2
    where " Gamma |= t ~: T " := (ok_term Gamma t T).
    #[export]
     Hint Constructors ok_term : mcore.

  End Typing1.
End Typing.
