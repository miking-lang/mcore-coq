From TLC Require Import LibString LibLN.
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

    with ok_env : env -> Prop :=
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

    Lemma ok_env_ok :
      forall Gamma,
        ok_env Gamma ->
        ok Gamma.
    Proof. introv Henv ; induction* Henv. Qed.
    #[export]
     Hint Resolve ok_env_ok : mcore.

    Lemma ok_kind_weakening :
      forall G3 G1 G2 k,
        ok_kind (G1 & G3) k ->
        ok_kind (G1 & G2 & G3) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_type_weakening :
      forall G3 G1 G2 T k,
        G1 & G3 |= T ~:: k ->
        ok_env (G1 & G2 & G3) ->
        G1 & G2 & G3 |= T ~:: k.
    Proof.
      introv Hk Henv.
      remember (G1 & G3) as Gamma. gen G3.
      induction* Hk; intros; substs.
      { Case "TyFVar". constructors*. apply* binds_weaken. }
      { Case "TyAll". apply_fresh* KAll. apply* ok_kind_weakening.
        apply_ih_bind* H1.
        constructor*. apply* ok_kind_weakening. }
    Qed.

    Lemma ok_env_ok_type :
      forall Gamma x T,
        ok_env Gamma ->
        binds x (BindVar T) Gamma ->
        Gamma |= T ~:: KiType.
    Proof.
      introv Henv Hbind.
      induction* Henv ; try (binds_cases Hbind ; apply_empty* ok_type_weakening).
      { Case "EnvEmpty". false. apply* binds_empty_inv. }
      { Case "EnvVar". inverts* EQ. }
    Qed.

    Lemma ok_type_lct :
      forall Gamma T k,
        Gamma |= T ~:: k ->
        lct T.
    Proof. introv Hk ; induction* Hk. Qed.
    #[export]
     Hint Resolve ok_type_lct : mcore.

    Lemma ok_term_lct :
      forall Gamma t T,
        Gamma |= t ~: T ->
        lct T.
    Proof with eauto using ok_env_ok_type, ok_type_lct.
      introv hasType.
      induction* hasType...
      { Case "TmLam". constructors...
        pick_fresh_gen L y... }
      { Case "TmApp". inverts* IHhasType1. }
      { Case "TmTyLam". inverts* IHhasType.
        assert(Hlct: lct ty2)...
        pick_fresh X. rewrite *(@tsubst_intro X).
        apply* tsubst_lct. }
    Qed.
    #[export]
     Hint Resolve ok_term_lct : mcore.

    Lemma ok_term_lc :
      forall Gamma t T,
        Gamma |= t ~: T ->
        lc t.
    Proof with eauto using ok_term_lct, ok_type_lct with mcore.
      introv Htype.
      induction* Htype; intros.
    Qed.
    #[export]
     Hint Resolve ok_term_lc : mcore.

    Lemma ok_env_push :
      forall G1 x b,
        ok_env (G1 & x ~ b) ->
        ok_env G1.
    Proof.
      introv Hwf.
      inverts Hwf ; try (apply eq_push_inv in H; inverts H as []; substs*).
      false. apply *empty_push_inv.
    Qed.

    Lemma ok_type_ok_env :
      forall Gamma T k,
        Gamma |= T ~:: k ->
        ok_env Gamma.
    Proof.
      introv hasType.
      induction* hasType; pick_fresh_gen L x;
        eauto using ok_env_push.
    Qed.
    #[export]
     Hint Resolve ok_type_ok_env : mcore.

    Lemma ok_term_ok_env :
      forall Gamma t T,
        Gamma |= t ~: T ->
        ok_env Gamma.
    Proof.
      introv hasType.
      induction* hasType; pick_fresh_gen L x;
        eauto using ok_env_push.
    Qed.
    #[export]
     Hint Resolve ok_term_ok_env : mcore.

    Lemma ok_term_weakening :
      forall G3 G2 G1 t T,
        G1 & G3 |= t ~: T ->
        ok_env (G1 & G2 & G3) ->
        G1 & G2 & G3 |= t ~: T.
    Proof.
      introv hasType Henv. remember (G1 & G3) as H. gen G3.
      induction hasType; intros; substs*.
      { Case "TmFVar". constructors*. apply* binds_weaken. }
      { Case "TmLam". apply_fresh* TLam as y.
        - apply* ok_type_weakening.
        - apply_ih_bind* H1.
          constructors*.
          apply* ok_type_weakening. }
      { Case "TmTyLam". apply_fresh* TTyLam as X.
        - apply* ok_kind_weakening.
        - apply_ih_bind* H1. constructors*. apply* ok_kind_weakening. }
      { Case "TmTyApp". constructors*. apply* ok_type_weakening. }
    Qed.

    Lemma ok_data_strengthening :
      forall G1 G2 x T d,
        ok_data (G1 & x ~ BindVar T & G2) d ->
        ok_data (G1 & G2) d.
    Proof.
      introv Hd. unfolds ok_data.
      splits*. introv Hbind.
      lets [Hbind' Hk]: (proj2 Hd) Hbind.
      splits.
      - binds_cases Hbind' ; auto.
      - introv Hkin. lets [ ? (? & Hbindk) ] : Hk Hkin.
        binds_cases Hbindk ; eauto.
    Qed.

    Lemma ok_kind_strengthening :
      forall G1 G2 x T k,
        ok_kind (G1 & x ~ BindVar T & G2) k ->
        ok_kind (G1 & G2) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_type_strengthening :
      forall G1 G2 x T1 T2 k,
        G1 & x ~ BindVar T2 & G2 |= T1 ~:: k ->
        ok_env (G1 & G2) ->
        G1 & G2 |= T1 ~:: k.
    Proof.
      introv Htk. remember (G1 & x ~ BindVar T2 & G2) as G. gen G2.
      induction Htk; intros; substs*.
      { Case "TyFVar". constructors*.
        binds_cases H0 ; auto. }
      { Case "TyAll". apply_fresh* KAll as X.
        apply* ok_kind_strengthening.
        apply_ih_bind* H1. constructor*. apply* ok_kind_strengthening. }
    Qed.

    Lemma ok_env_con_inv :
      forall Gamma K d ty T,
        ok_env (Gamma & K ~ BindCon d ty T) ->
        ok_data Gamma d /\ Gamma |= ty ~:: KiType /\ binds T BindTName Gamma.
    Proof.
      introv Henv.
      inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; splits* ; fequals).
      false. apply* empty_push_inv.
    Qed.

    Lemma ok_env_tvar_inv :
      forall Gamma X k,
        ok_env (Gamma & X ~ BindTVar k) ->
        ok_kind Gamma k.
    Proof.
      introv Henv.
      inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; fequals).
      false. apply* empty_push_inv.
    Qed.

    Lemma ok_env_var_inv :
      forall Gamma x T,
        ok_env (Gamma & x ~ BindVar T) ->
        Gamma |= T ~:: KiType.
    Proof.
      introv Henv.
      inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; fequals).
      false. apply* empty_push_inv.
    Qed.

    Lemma ok_env_strengthening :
      forall G1 x T G3,
        ok_env (G1 & x ~ BindVar T & G3) ->
        ok_env (G1 & G3).
    Proof.
      introv Henv. induction G3 using env_ind.
      { Case "Empty". rewrite concat_empty_r in *. apply* ok_env_push. }
      { Case "Push". rewrite concat_assoc in *.
        specializes IHG3 (ok_env_push _ _ _ Henv).
        lets [? Hdisj] : ok_push_inv (ok_env_ok _ Henv).
        destruct v.
        { SCase "BindTName". constructor~. }
        { SCase "BindCon". forwards [ Hd (Htk & HT)]: ok_env_con_inv Henv.
          constructor~.
          - applys ok_data_strengthening Hd.
          - applys* ok_type_strengthening Htk.
          - binds_cases HT ; auto. }
        { SCase "BindTVar". forwards Hk: ok_env_tvar_inv Henv.
          constructor~. applys ok_kind_strengthening Hk. }
        { SCase "BindVar". forwards Htk: ok_env_var_inv Henv.
          constructor~. applys* ok_type_strengthening Htk. }
        { SCase "BindMatch". constructor~. } }
    Qed.

    Lemma ok_term_subst :
      forall G2 G1 x T1 T2 t1 t2,
        G1 & x ~ BindVar T2 & G2 |= t1 ~: T1 ->
        G1 |= t2 ~: T2 ->
        G1 & G2 |= [x => t2]t1 ~: T1.
    Proof with eauto using ok_term_lc, ok_env_strengthening, ok_type_strengthening with mcore.
      introv hasType1 hasType2.
      remember (G1 & x ~ BindVar T2 & G2) as G. gen G2.
      induction hasType1; intros; simpls; substs...
      { Case "TmFVar". solve_var.
        - binds_get H0... apply_empty ok_term_weakening...
        - binds_cases H0... }
      { Case "TmLam". apply_fresh* TLam as y...
        rewrite subst_open_comm... apply_ih_bind* H1. }
      { Case "TmTyLam". apply_fresh* TTyLam as X. apply* ok_kind_strengthening.
        rewrite* topen_t_subst_comm. apply_ih_bind* H1. }
      { Case "TmTyApp". constructors*. apply* ok_type_strengthening. }
    Qed.

    Lemma ok_data_tvar_strengthening :
      forall G1 G2 x k d,
        ok_data (G1 & x ~ BindTVar k & G2) d ->
        ok_data (G1 & G2) d.
    Proof.
      introv Hd. unfolds ok_data.
      splits*. introv Hbind.
      lets [Hbind' Hk]: (proj2 Hd) Hbind.
      splits.
      - binds_cases Hbind' ; auto.
      - introv Hkin. lets [ ? (? & Hbindk) ] : Hk Hkin.
        binds_cases Hbindk ; eauto.
    Qed.

    Lemma ok_data_bsubst :
      forall G1 G2 X T d,
        ok_data (G1 & G2) d ->
        ok_data (G1 & map (bsubst X T) G2) d.
    Proof.
      introv Hd. unfolds ok_data.
      splits*. introv Hbind.
      lets [Hbind' Hk]: (proj2 Hd) Hbind.
      splits.
      - binds_cases Hbind' ; auto.
        replaces BindTName with (bsubst X T BindTName) ; auto.
      - introv Hkin. lets [ d' (ty & Hbindk) ] : Hk Hkin.
        binds_cases Hbindk ; eauto.
        exists d' ({X => T} ty).
        replaces (BindCon d' ({X => T} ty) T0) with (bsubst X T (BindCon d' ty T0)) ; auto.
    Qed.

    Lemma ok_kind_tvar_strengthening :
      forall G1 G2 x k' k,
        ok_kind (G1 & x ~ BindTVar k' & G2) k ->
        ok_kind (G1 & G2) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_kind_bsubst :
      forall G1 G2 X T k,
        ok_kind (G1 & G2) k ->
        ok_kind (G1 & map (bsubst X T) G2) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_type_tsubst :
      forall G1 G2 X T1 T2 k k',
        G1 & X ~ BindTVar k' & G2 |= T1 ~:: k ->
        G1 |= T2 ~:: k' ->
        ok_env (G1 & map (bsubst X T2) G2) ->
        G1 & map (bsubst X T2) G2 |= {X => T2} T1 ~:: k.
    Proof with eauto with mcore.
      introv Hkt1 Hkt2 Henv.
      remember (G1 & X ~ BindTVar k' & G2) as G. gen G2.
      induction Hkt1; intros; substs; simpls*.
      { Case "TyFVar". solve_var.
        + binds_get H0. lets* [Hok ?] : ok_concat_inv (ok_env_ok _ Henv).
          apply_empty* ok_type_weakening.
        + binds_cases H0...
          constructors*. apply binds_concat_right.
          replaces (BindTVar k) with (bsubst X T2 (BindTVar k))... }
      { Case "TyAll". assert (Hk : ok_kind (G1 & map (bsubst X T2) G2) k).
        apply* ok_kind_bsubst. apply* ok_kind_tvar_strengthening.
        apply_fresh* KAll.
        assert (lct T2) by apply* ok_type_lct.
        rewrite~ tsubst_topen_comm.
        replaces (G1 & map (bsubst X T2) G2 & y ~ BindTVar k)
          with (G1 & map (bsubst X T2) (G2 & y ~ BindTVar k))...
        + autorewrite with rew_env_map rew_env_concat ; auto.
        + apply~ H1.
          * autorewrite with rew_env_concat ; auto.
          * autorewrite with rew_env_map rew_env_concat... }
    Qed.

    Lemma bsubst_ok_env :
      forall G1 G2 X T2 k,
        G1 |= T2 ~:: k ->
        ok_env (G1 & X ~ BindTVar k & G2) ->
        ok_env (G1 & map (bsubst X T2) G2).
    Proof.
      introv Htk Henv.
      induction G2 using env_ind.
      { Case "Empty". autorewrite with rew_env_map rew_env_concat in *.
        apply* ok_env_push. }
      { Case "Push". autorewrite with rew_env_map rew_env_concat in *.
        specializes IHG2 (ok_env_push _ _ _ Henv).
        lets [? Hdisj] : ok_push_inv (ok_env_ok _ Henv).
        destruct v.
        { SCase "BindTName". constructor~. }
        { SCase "BindCon". forwards (Hd & Htk' & HT): ok_env_con_inv Henv.
          constructor~.
          - applys ok_data_bsubst. apply* ok_data_tvar_strengthening.
          - applys* ok_type_tsubst Htk.
          - binds_cases HT ; auto.
            replaces BindTName with (bsubst X T2 BindTName) ; auto. }
        { SCase "BindTVar". forwards Hk: ok_env_tvar_inv Henv.
          constructor~. applys ok_kind_bsubst. apply* ok_kind_tvar_strengthening. }
        { SCase "BindVar". forwards Htk': ok_env_var_inv Henv.
          constructor~. applys* ok_type_tsubst Htk'. }
        { SCase "BindMatch". constructor~. } }
    Qed.

    Lemma ok_env_concat :
      forall G1 G2,
        ok_env (G1 & G2) ->
        ok_env G1.
    Proof with eauto.
      introv Henv.
      induction G2 using env_ind.
      { Case "Empty". rew_env_concat in *... }
      { Case "Push". apply IHG2. rew_env_concat in *.
        apply* ok_env_push. }
    Qed.

    Lemma ok_type_notin :
      forall Gamma T k X,
        Gamma |= T ~:: k ->
        X # Gamma ->
        X \notin ftv T.
    Proof.
      introv Htk Hfresh.
      induction Htk; simpls*.
      { Case "TyFVar". intros contra.
        rewrite in_singleton in contra. substs.
        apply get_none in Hfresh.
        apply binds_get in H0.
        fequals. }
      { Case "TyAll". pick_fresh Y.
        forwards~ Hnin: H0 Y.
        applys~ topen_notin Y. }
    Qed.

    Lemma env_bsubst_fresh :
      forall Gamma X T2,
        ok_env Gamma ->
        X # Gamma ->
        Gamma = map (bsubst X T2) Gamma.
    Proof with eauto using ok_env_push.
      introv Henv Hfresh.
      induction Gamma using env_ind.
      { Case "Empty". rewrite~ map_empty. }
      { Case "Push". autorewrite with rew_env_map.
        rewrite <- IHGamma...
        destruct~ v ; repeat fequals ; unfold bsubst ; rewrite* tsubst_fresh.
        { SCase "BindCon".
          apply ok_env_con_inv in Henv as (? & Hkt & ?).
          apply* ok_type_notin. }
        { SCase "BindVar".
          apply ok_env_var_inv in Henv.
          apply* ok_type_notin. } }
    Qed.

    Lemma ok_term_tsubst :
      forall G2 G1 t k T1 T2 X,
        G1 & X ~ BindTVar k & G2 |= t ~: T1 ->
        G1 |= T2 ~:: k ->
        G1 & map (bsubst X T2) G2 |= [{X => T2}]t ~: ({X => T2}T1).
    Proof with eauto using ok_env_strengthening, bsubst_ok_env with mcore.
      introv hasType Henv.
      remember (G1 & X ~ BindTVar k & G2) as G. gen G2.
      induction hasType; intros; simpls; substs...
      { Case "TmFVar".
        binds_cases H0 ; constructors ;
          replaces (BindVar ({X => T2} ty)) with (bsubst X T2 (BindVar ty))...
        apply ok_env_concat in H.
        assert (X # G1) by apply* ok_push_inv.
        rewrite* (@env_bsubst_fresh G1 X T2). }
      { Case "TmLam". apply_fresh* TLam as x.
        + apply* ok_type_tsubst. apply* bsubst_ok_env.
        + rewrite tsubst_t_open_comm.
          replaces (G1 & map (bsubst X T2) G2 & x ~ BindVar ({X => T2}ty1))
            with (G1 & map (bsubst X T2) (G2 & x ~ BindVar ty1)).
          autorewrite with rew_env_map rew_env_concat ; auto.
          apply~ H1. rewrite~ concat_assoc. }
      { Case "TmTyLam". apply_fresh* TTyLam.
        + apply ok_kind_bsubst. apply* ok_kind_tvar_strengthening.
        + replaces (G1 & map (bsubst X T2) G2 & y ~ BindTVar k0)
            with (G1 & map (bsubst X T2) (G2 & y ~ BindTVar k0)).
          autorewrite with rew_env_map rew_env_concat ; auto.
          rewrite~ tsubst_topen_comm...
          rewrite topen_t_tsubst_comm...
          apply~ H1. rewrite~ concat_assoc. }
      { Case "TmTyApp".
        rewrite tsubst_topen_distr... constructors*.
        apply* ok_type_tsubst. }
    Qed.

  End Typing.
End Typing.
