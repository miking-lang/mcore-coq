From TLC Require Import LibString LibLN LibEnv.
From MCore Require Import Syntax Tactics.

Module Typing (P : PAT).
  Module S := Syntax P.
  Export S.

  Module Type PATCHECK.
    Parameter ok_pat : env -> pat -> type -> env -> Prop.
    Parameter matches_contradictory : env -> Prop.
    Parameter pats_compatible : list pat -> type -> Prop.
    Parameter pats_exhaustive : list pat -> type -> Prop.
  End PATCHECK.

  Module Typing (PC : PATCHECK).
    Export PC.

    (*********************************)
    (** TYPING RELATION DEFINITIONS **)
    (*********************************)

    Definition ok_data (Gamma : env) (d : data) : Prop :=
      ok d /\
      forall T cons,
        binds T cons d ->
        binds T BindTName Gamma /\
          forall K,
            K \in cons -> exists d ty, binds K (BindCon d ty T) Gamma
    .

    Inductive ok_kind : env -> kind -> Prop :=
    | TypeOk : forall {Gamma : env},
        ok_kind Gamma KiType
    (* | DataOk : forall {Gamma : env} {d : data}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_kind Gamma (KiData d) *)
    .
    #[export]
     Hint Constructors ok_kind : mcore.

    Reserved Notation "Gamma |= T ~:: k " (at level 50).
    Inductive ok_type : env -> type -> kind -> Prop :=
    | KVar : forall Gamma tv k,
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
    where " Gamma |= T ~:: k " := (ok_type Gamma T k)
    .
    #[export]
     Hint Constructors ok_type : mcore.

    Inductive ok_env : env -> Prop :=
    | EnvEmpty : ok_env empty
    | EnvTName : forall Gamma X, ok_env Gamma -> X # Gamma -> ok_env (Gamma & X ~ BindTName)
    | EnvCon   :
      forall Gamma K d ty T,
        ok_env Gamma ->
        K # Gamma ->
        ok_data Gamma d ->
        Gamma |= ty ~:: KiType ->
        binds T BindTName Gamma ->
        ok_env (Gamma & K ~ BindCon d ty T)
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
    | EnvMatch : forall Gamma M m,
        ok_env Gamma ->
        M # Gamma ->
        ok_env (Gamma & M ~ BindMatch m)
    .
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
    where " Gamma |= t ~: T " := (ok_term Gamma t T).
    #[export]
     Hint Constructors ok_term : mcore.


    (**************************)
    (** PROPERTIES OF TYPING **)
    (**************************)

    Lemma ok_type_lct :
      forall Gamma T k,
        Gamma |= T ~:: k ->
        lct T.
    Proof. introv Hk ; induction* Hk. Qed.

    Lemma ok_env_ok :
      forall Gamma,
        ok_env Gamma ->
        ok Gamma.
    Proof. introv Hwf ; induction* Hwf. Qed.

    Lemma ok_kind_weakening :
      forall G3 G1 G2 k,
        ok_kind (G1 & G3) k ->
        ok_kind (G1 & G2 & G3) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_type_weakening :
      forall G3 G1 G2 T k,
        ok_type (G1 & G3) T k ->
        ok_env (G1 & G2 & G3) ->
        ok_type (G1 & G2 & G3) T k.
    Proof.
      introv Hk Henv.
      remember (G1 & G3) as Gamma. gen G3.
      induction* Hk; intros; substs.
      - constructors*. apply* binds_weaken.
        apply* ok_env_ok.
      - apply_fresh* KAll. apply* ok_kind_weakening.
        apply_ih_bind* H1.
        constructor*. apply* ok_kind_weakening.
    Qed.

    Lemma ok_env_ok_type :
      forall Gamma x T,
        ok_env Gamma ->
        binds x (BindVar T) Gamma ->
        Gamma |= T ~:: KiType.
    Proof.
      introv Henv Hbind.
      induction* Henv ; try (binds_cases Hbind ; apply_empty* ok_type_weakening).
      - false. apply* binds_empty_inv.
      - inverts* EQ.
    Qed.


  End Typing.
End Typing.
