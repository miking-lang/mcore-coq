From MCore Require Import Syntax Env Tactics.
From TLC Require Import LibList LibSet.

Module Typing (P : PAT).
  Module E := Env P.
  Export E.

  Module Type PATCHECK.
    Parameter ok_pat : env -> pat -> type -> env -> Prop.
    Parameter matches_contradictory : env -> Prop.
    Parameter pats_compatible : list pat -> type -> Prop.
    Parameter pats_exhaustive : list pat -> type -> Prop.
  End PATCHECK.

  Module Typing (PC : PATCHECK).
    Export PC.

    Definition ok_data (Gamma : env) (d : data) : Prop :=
      forall (T : tname),
        T \indom d ->
        tname_in T (tnames Gamma) /\
          forall (K : con),
            K \in (d[T] : set con) ->
                  exists d ty, con_in K d ty T (cons Gamma)
    .

    Inductive ok_kind : env -> kind -> Prop :=
    | KiType' : forall {Gamma : env},
        ok_kind Gamma KiType
    (* | KiData' : forall {Gamma : env} {d : data}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_kind Gamma (KiData d) *)
    .
    #[export]
     Hint Constructors ok_kind : mcore.

    Inductive ok_type : env -> type -> kind -> Prop :=
    | TyFVar' : forall {Gamma : env} {tv : tvar} {k : kind},
        tvar_in tv k (tvars Gamma) ->
        ok_type Gamma (TyFVar tv) k
    | TyArr' : forall {Gamma : env} {ty1 ty2 : type},
        ok_type Gamma ty1 KiType ->
        ok_type Gamma ty2 KiType ->
        ok_type Gamma (TyArr ty1 ty2) KiType
    | TyAll' : forall {Gamma : env} {k : kind} {ty : type},
        ok_type (BindTvar k :: Gamma) (ty_open ty) KiType ->
        ok_type Gamma (TyAll k ty) KiType
    (* | TyProd' : forall {Gamma : env} {ty1 ty2 : type}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_type Gamma (TyProd ty1 ty2) KiType *)
    (* | TyCon' : forall {Gamma : env} {ty : type} {d : data} {T : tname}, *)
    (*     ok_type Gamma ty (KiData d) -> *)
    (*     T \indom d -> *)
    (*     ok_type Gamma (TyCon ty T) KiType *)
    (* | TySem' : forall {Gamma : env} {ty1 ty2 : type} {ps : list pat}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_type Gamma (TySem ty1 ty2 ps) KiType *)
    (* | TyData' : forall {Gamma : env} {d : data}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_type Gamma (TyData d) (KiData d) *)
    (* | TyDataSub' : forall {Gamma : env} {ty : type} {d1 d2 : data}, *)
    (*     ok_type Gamma ty (KiData d1) -> *)
    (*     d2 \c d1 -> *)
    (*     (forall {T : tname}, d2[T] \c d1[T]) -> *)
    (*     ok_type Gamma ty (KiData d2) *)
    .
    #[export]
     Hint Constructors ok_type : mcore.

    Inductive ok_env : env -> Prop :=
    | EnvEmpty : ok_env empty_env
    | EnvTname : forall Gamma, ok_env Gamma -> ok_env (BindTname :: Gamma)
    | EnvCon   :
      forall Gamma d ty T,
        ok_env Gamma ->
        ok_data Gamma d ->
        ok_type Gamma ty KiType ->
        tname_in T (tnames Gamma) ->
        ok_env (BindCon d ty T :: Gamma)
    | EnvTvar : forall Gamma k,
        ok_env Gamma ->
        ok_kind Gamma k ->
        ok_env (BindTvar k :: Gamma)
    | EnvVar : forall Gamma ty,
        ok_env Gamma ->
        ok_type Gamma ty KiType ->
        ok_env (BindVar ty :: Gamma)
    | EnvMatch : forall Gamma m,
        ok_env Gamma ->
        ok_env (BindMatch m :: Gamma)
    | EnvSkipTvar : forall Gamma,
        ok_env Gamma ->
        ok_env (SkipTvar :: Gamma)
    | EnvSkipVar : forall Gamma,
        ok_env Gamma ->
        ok_env (SkipVar :: Gamma)
    .
    #[export]
     Hint Constructors ok_env : mcore.

    Inductive ok_term : env -> term -> type -> Prop :=
    | TmFVar' : forall {Gamma : env} {x : var} {ty : type},
        ok_env Gamma ->
        var_in x ty (vars Gamma) ->
        ok_term Gamma (TmFVar x) ty
    | TmLam' : forall {Gamma : env} {ty1 ty2 : type} {t : term},
        ok_type Gamma ty1 KiType ->
        ok_term (BindVar ty1 :: Gamma) (tm_open t) ty2 ->
        ok_term Gamma (TmLam ty1 t) (TyArr ty1 ty2)
    | TmApp' : forall {Gamma : env} {ty1 ty2 : type} {t1 t2 : term},
        ok_term Gamma t1 (TyArr ty1 ty2) ->
        ok_term Gamma t2 ty1 ->
        ok_term Gamma (TmApp t1 t2) ty2
    | TmTyLam' : forall {Gamma : env} {k : kind} {ty : type} {t : term},
        ok_kind Gamma k ->
        ok_term (BindTvar k :: Gamma) (tm_ty_open t) (ty_open ty) ->
        ok_term Gamma (TmTyLam k t) (TyAll k ty)
    | TmTyApp' : forall {Gamma : env} {k : kind} {ty1 ty2 : type} {t : term},
        ok_term Gamma t (TyAll k ty1) ->
        ok_type Gamma ty2 k ->
        ok_term Gamma (TmTyApp t ty2) (ty_bsubst ty1 0 ty2)
    (* | TmFix' : forall {Gamma : env} {ty : type} {t : term}, *)
    (*     ok_term Gamma t (TyArr ty ty) -> *)
    (*     ok_term Gamma (TmFix t) ty *)
    (* | TmProd' : forall {Gamma : env} {ty1 ty2 : type} {t1 t2 : term}, *)
    (*     ok_term Gamma t1 ty1 -> *)
    (*     ok_term Gamma t2 ty2 -> *)
    (*     ok_term Gamma (TmProd t1 t2) (TyProd ty1 ty2) *)
    (* | TmProj1' : forall {Gamma : env} {ty1 ty2 : type} {t : term}, *)
    (*     ok_term Gamma t (TyProd ty1 ty2) -> *)
    (*     ok_term Gamma (TmProj F1 t) ty1 *)
    (* | TmProj2' : forall {Gamma : env} {ty1 ty2 : type} {t : term}, *)
    (*     ok_term Gamma t (TyProd ty1 ty2) -> *)
    (*     ok_term Gamma (TmProj F2 t) ty2 *)
    (* | TmCon' : forall {Gamma : env} {K : con} {d : data} *)
    (*                   {ty1 ty2 : type} {T : tname} {t : term}, *)
    (*     con_in K d ty1 T Gamma.(cons) -> *)
    (*     ok_type Gamma ty2 (KiData d) -> *)
    (*     ok_type Gamma ty2 (KiData (T \:= \{K})) -> *)
    (*     ok_term Gamma t (ty_subst ty1 ty2) -> *)
    (*     ok_term Gamma (TmCon K ty2 t) (TyCon ty2 T) *)
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
    (* | TmType' : forall {Gamma : env} {t : term} {ty : type}, *)
    (*     ok_type Gamma ty KiType -> *)
    (*     ok_term (Gamma <| tnames ::= S |>) t ty *)
    (* | TmConDef' : forall {Gamma : env} {d : data} *)
    (*                      {ty1 ty2 : type} {T : tname} *)
    (*                      {t : term}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_type (Gamma <| tvars ::= fun tv => KiData d :: tv |>) *)
    (*             ty1 KiType -> *)
    (*     ok_term (Gamma <| cons ::= fun Ks => (d, ty1, T) :: Ks |>) *)
    (*             t ty2 -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_term Gamma (TmConDef d ty1 T t) ty2 *)
    (* | TmSem' : forall {Gamma : env} {ty1 ty2 : type} *)
    (*                   {cases : list (pat * term)}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     Forall (fun (c : pat * term) => *)
    (*               exists (vs : var_env), *)
    (*                 ok_pat Gamma (fst c) ty1 vs /\ *)
    (*                   ok_term (Gamma <| vars ::= fun vs' => vs ++ vs' |>) *)
    (*                           (snd c) ty2) *)
    (*            cases -> *)
    (*     pats_compatible (LibList.map fst cases) ty1 -> *)
    (*     ok_term *)
    (*       Gamma *)
    (*       (TmSem ty1 cases) *)
    (*       (TySem ty1 ty2 (LibList.map fst cases)) *)
    (* | TmComp' : forall {Gamma : env} {ty1 ty2 : type} *)
    (*                    {t1 t2 : term} {ps1 ps2 : list pat}, *)
    (*     ok_term Gamma t1 (TySem ty1 ty2 ps1) -> *)
    (*     ok_term Gamma t2 (TySem ty1 ty2 ps2) -> *)
    (*     pats_compatible (ps1 ++ ps2) ty1 -> *)
    (*     ok_term Gamma (TmComp t1 t2) (TySem ty1 ty2 (ps1 ++ ps2)) *)
    (* | TmSemApp' : forall {Gamma : env} {ty1 ty2 : type} *)
    (*                      {t1 t2 : term} {ps : list pat}, *)
    (*     ok_term Gamma t1 (TySem ty1 ty2 ps) -> *)
    (*     ok_term Gamma t2 ty1 -> *)
    (*     pats_exhaustive ps ty1 -> *)
    (*     ok_term Gamma (TmSemApp t1 t2) ty2 *)
    .
    #[export]
     Hint Constructors ok_term : mcore.
  End Typing.
End Typing.
