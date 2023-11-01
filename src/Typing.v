From TLC Require Import LibString LibList LibLN.
From MCore Require Import Syntax Tactics.
Import LibList.LibListNotation.

Notation mem := LibList.mem.

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
        ok_type Gamma ty1 KiType ->
        ok_type Gamma ty2 KiType ->
        ok_type Gamma (TyProd ty1 ty2) KiType
    | KCon : forall Gamma ty d T Ks,
        Gamma |= ty ~:: KiData d ->
        mem (FTName T, Ks) d ->
        Gamma |= TyCon ty (FTName T) ~:: KiType
    (* | TySem' : forall {Gamma : env} {ty1 ty2 : type} {ps : list pat}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_type Gamma (TySem ty1 ty2 ps) KiType *)
    | KData : forall Gamma d,
        ok_env Gamma ->
        ok_data Gamma d ->
        Gamma |= TyData d ~:: KiData d
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
        ok_term Gamma t (TyArr ty ty) ->
        ok_term Gamma (TmFix t) ty
    | TProd : forall Gamma ty1 ty2 t1 t2,
        ok_term Gamma t1 ty1 ->
        ok_term Gamma t2 ty2 ->
        ok_term Gamma (TmProd t1 t2) (TyProd ty1 ty2)
    | TProj1 : forall Gamma ty1 ty2 t,
        ok_term Gamma t (TyProd ty1 ty2) ->
        ok_term Gamma (TmProj F1 t) ty1
    | TProj2 : forall Gamma ty1 ty2 t,
        ok_term Gamma t (TyProd ty1 ty2) ->
        ok_term Gamma (TmProj F2 t) ty2
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
        lct ty ->
        (forall T, T \notin L ->
              Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty) ->
        Gamma |= TmType t ~: ty
    | TConDef : forall L Gamma d ty1 ty2 T t,
        ok_data Gamma d ->
        (forall X, X \notin L ->
              Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty1 ~:: KiType) ->
        binds T BindTName Gamma ->
        lct ty2 ->
        (forall K, K \notin L ->
              Gamma & K ~ BindCon d ty1 (FTName T) |= Kopen_t 0 (FCon K) t ~: ty2) ->
        Gamma |= TmConDef d ty1 (FTName T) t ~: ty2
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

    Lemma ok_data_weakening :
      forall G3 G1 G2 d,
        ok_data (G1 & G3) d ->
        ok_env  (G1 & G2 & G3) ->
        ok_data (G1 & G2 & G3) d.
    Proof.
      introv Hd Henv.
      remember (G1 & G3) as Gamma eqn:HGamma.
      assert (Hok : ok (G1 & G2)) by applys* ok_concat_inv_l G3.
      induction Hd ; constructor*.
      - substs ; apply* binds_weaken.
      - induction H1 ; substs ; constructors*.
        apply* binds_weaken.
    Qed.

    Lemma ok_kind_weakening :
      forall G3 G1 G2 k,
        ok_kind (G1 & G3) k ->
        ok_env  (G1 & G2 & G3) ->
        ok_kind (G1 & G2 & G3) k.
    Proof.
      introv Hk.
      remember (G1 & G3) as Gamma eqn:HGamma.
      destruct Hk; subst*. constructor. apply* ok_data_weakening.
    Qed.

    Lemma ok_type_weakening :
      forall G3 G1 G2 T k,
        G1 & G3 |= T ~:: k ->
        ok_env (G1 & G2 & G3) ->
        G1 & G2 & G3 |= T ~:: k.
    Proof.
      introv Htk Henv.
      remember (G1 & G3) as Gamma. gen G3.
      induction* Htk; intros; substs.
      { Case "TyFVar". constructors*. apply* binds_weaken. }
      { Case "TyAll". apply_fresh* KAll. apply* ok_kind_weakening.
        apply_ih_bind* H1.
        constructor*. apply* ok_kind_weakening. }
      { Case "TyData". constructors*. apply* ok_data_weakening. }
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

    Lemma ok_data_lcd : forall Gamma d, ok_data Gamma d -> lcd d.
    Proof.
      introv Hd. unfolds.
      induction Hd ; rew_listx*. splits*. splits*.
      induction H1 ; rew_listx*.
    Qed.
    #[export]
     Hint Resolve ok_data_lcd : mcore.

    Lemma ok_kind_lck : forall Gamma k, ok_kind Gamma k -> lck k.
    Proof. introv Hk. destruct* Hk. Qed.
    #[export]
     Hint Resolve ok_kind_lck : mcore.

    Lemma ok_type_lct :
      forall Gamma T k,
        Gamma |= T ~:: k ->
        lct T.
    Proof. introv Htk ; induction* Htk. Qed.
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
      { Case "TmFix". inverts* IHhasType. }
      { Case "TmProd". inverts* IHhasType. }
      { Case "TmProj". inverts* IHhasType. }
    Qed.
    #[export]
     Hint Resolve ok_term_lct : mcore.

    Lemma ok_term_lc :
      forall Gamma t T,
        Gamma |= t ~: T ->
        lc t.
    Proof. introv Htype; induction* Htype. Qed.
    #[export]
     Hint Resolve ok_term_lc : mcore.

    Lemma ok_env_push :
      forall G1 x b,
        ok_env (G1 & x ~ b) ->
        ok_env G1.
    Proof.
      introv Henv.
      inverts Henv ; try (apply eq_push_inv in H; inverts H as []; substs*).
      false. apply *empty_push_inv.
    Qed.

    Lemma ok_type_ok_env :
      forall Gamma T k,
        Gamma |= T ~:: k ->
        ok_env Gamma.
    Proof.
      introv hasType.
      induction* hasType ; pick_fresh_gen L x; eauto using ok_env_push.
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
    Proof with eauto using ok_type_weakening, ok_kind_weakening, ok_data_weakening with mcore.
      introv hasType Henv. remember (G1 & G3) as H. gen G3.
      induction hasType; intros; substs...
      { Case "TmFVar". constructors~. apply* binds_weaken. }
      { Case "TmLam". apply_fresh* TLam as y...
        apply_ih_bind H1 ; auto. constructor... }
      { Case "TmTyLam". apply_fresh* TTyLam as X...
        apply_ih_bind H1 ; auto. constructor... }
      { Case "TmCon". constructors...
        apply* binds_weaken. }
      { Case "TmType". apply_fresh TType as T...
        apply_ih_bind H1 ; auto. constructor... }
      { Case "TmConDef". apply_fresh TConDef as K...
        - apply_ih_bind ok_type_weakening...
        - apply* binds_weaken.
        - apply_ih_bind H4 ; auto.
          apply_fresh EnvCon as X...
          + apply_ih_bind ok_type_weakening...
          + apply* binds_weaken. }
    Qed.

    Lemma ok_data_strengthening :
      forall G1 G2 x T d,
        ok_data (G1 & x ~ BindVar T & G2) d ->
        ok_data (G1 & G2) d.
    Proof.
      introv Hd.
      remember (G1 & x ~ BindVar T & G2) as Gamma.
      induction Hd ; constructor*.
      - substs ; binds_cases H0 ; auto.
      - induction* H1 ; substs ; constructors*.
        binds_cases H3 ; eauto.
    Qed.

    Lemma ok_kind_strengthening :
      forall G1 G2 x T k,
        ok_kind (G1 & x ~ BindVar T & G2) k ->
        ok_kind (G1 & G2) k.
    Proof.
      introv Hk. remember (G1 & x ~ BindVar T & G2) as G.
      destruct Hk ; substs*. constructor. apply* ok_data_strengthening.
    Qed.

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
      { Case "TyData". constructor*. apply* ok_data_strengthening. }
    Qed.

    Lemma ok_env_con_inv :
      forall Gamma K d ty T,
        ok_env (Gamma & K ~ BindCon d ty T) ->
        exists L T',
          T = FTName T'
          /\ ok_data Gamma d
          /\ (forall X, X \notin L -> Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty ~:: KiType)
          /\ binds T' BindTName Gamma.
    Proof.
      introv Henv.
      inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?)) ; try discriminate.
      - false. apply* empty_push_inv.
      - substs ; inverts* H5. exists* L T0.
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
        { SCase "BindCon". forwards (L & T' & Heq & Hd & Htk & HT): ok_env_con_inv Henv.
          substs. apply_fresh* EnvCon as K.
          - apply* ok_data_strengthening.
          - apply_ih_bind ok_type_strengthening ; eauto.
            constructor~. constructor~. apply* ok_data_strengthening.
          - binds_cases HT ; auto. }
        { SCase "BindTVar". forwards Hk: ok_env_tvar_inv Henv.
          constructor~. applys ok_kind_strengthening Hk. }
        { SCase "BindVar". forwards Htk: ok_env_var_inv Henv.
          constructor~. applys* ok_type_strengthening Htk. }
        (* { SCase "BindMatch". constructor~. } *)
      }
    Qed.

    Lemma ok_term_subst :
      forall G2 G1 x T1 T2 t1 t2,
        G1 & x ~ BindVar T2 & G2 |= t1 ~: T1 ->
        G1 |= t2 ~: T2 ->
        G1 & G2 |= [x => t2]t1 ~: T1.
    Proof with eauto using ok_data_strengthening, ok_kind_strengthening,
        ok_type_strengthening, ok_env_strengthening with mcore.
      introv hasType1 hasType2.
      remember (G1 & x ~ BindVar T2 & G2) as G. gen G2.
      induction hasType1; intros; simpls; substs...
      { Case "TmFVar". solve_var.
        - binds_get H0... apply_empty ok_term_weakening...
        - binds_cases H0... }
      { Case "TmLam". apply_fresh* TLam as y...
        rewrite subst_open_comm... apply_ih_bind* H1. }
      { Case "TmTyLam". apply_fresh* TTyLam as X...
        rewrite* topen_t_subst_comm. apply_ih_bind* H1. }
      { Case "TmTyApp". constructors... }
      { Case "TmCon". constructors... binds_cases H ; auto. }
      { Case "TmType". apply_fresh* TType as T...
        rewrite* Topen_t_subst_comm. apply_ih_bind* H1. }
      { Case "TmConDef". apply_fresh* TConDef as K...
        - apply_ih_bind ok_type_strengthening ; eauto. constructor...
        - binds_cases H1; auto.
        - rewrite* Kopen_t_subst_comm. apply_ih_bind* H4. }
    Qed.

    Lemma ok_data_tvar_strengthening :
      forall G1 G2 x k d,
        ok_data (G1 & x ~ BindTVar k & G2) d ->
        ok_data (G1 & G2) d.
    Proof.
      introv Hd.
      remember (G1 & x ~ BindTVar k & G2) as Gamma.
      induction Hd ; constructor*.
      - substs ; binds_cases H0 ; auto.
      - induction* H1 ; substs ; constructors*.
        binds_cases H3 ; eauto.
    Qed.

    Lemma ok_data_bsubst :
      forall G1 G2 X T d,
        ok_data (G1 & G2) d ->
        ok_data (G1 & map (bsubst X T) G2) d.
    Proof.
      introv Hd.
      remember (G1 & G2) as Gamma.
      induction Hd ; constructor*.
      - substs ; binds_cases H0 ; auto.
        replaces BindTName with (bsubst X T BindTName) ; auto.
      - induction* H1 ; substs.
        binds_cases H3 ; constructors*.
        replaces (BindCon d0 ({X => T} ty) T1) with (bsubst X T (BindCon d0 ty T1)) ; auto.
    Qed.

    Lemma ok_kind_tvar_strengthening :
      forall G1 G2 x k' k,
        ok_kind (G1 & x ~ BindTVar k' & G2) k ->
        ok_kind (G1 & G2) k.
    Proof.
      introv Hk. remember (G1 & x ~ BindTVar k' & G2) as Gamma.
      destruct* Hk. constructor. substs. apply* ok_data_tvar_strengthening.
    Qed.

    Lemma ok_kind_bsubst :
      forall G1 G2 X T k,
        ok_kind (G1 & G2) k ->
        ok_kind (G1 & map (bsubst X T) G2) k.
    Proof.
      introv Hk. remember (G1 & G2) as Gamma.
      destruct* Hk. constructor. substs. apply* ok_data_bsubst.
    Qed.

    Lemma ok_type_tsubst :
      forall G1 G2 X T1 T2 k k',
        G1 & X ~ BindTVar k' & G2 |= T1 ~:: k ->
        G1 |= T2 ~:: k' ->
        ok_env (G1 & map (bsubst X T2) G2) ->
        G1 & map (bsubst X T2) G2 |= {X => T2} T1 ~:: k.
    Proof with eauto using ok_data_bsubst, ok_kind_bsubst, ok_type_lct,
        ok_data_tvar_strengthening, ok_kind_tvar_strengthening with mcore.
      introv Htk1 Htk2 Henv.
      remember (G1 & X ~ BindTVar k' & G2) as G. gen G2.
      induction Htk1; intros; substs; simpls...
      { Case "TyFVar". solve_var.
        + binds_get H0. lets* [Hok ?] : ok_concat_inv (ok_env_ok _ Henv).
          apply_empty* ok_type_weakening.
        + constructors~. binds_cases H0...
          replaces (BindTVar k) with (bsubst X T2 (BindTVar k))... }
      { Case "TyAll". apply_fresh KAll... rewrite tsubst_topen_comm...
        replaces (BindTVar k) with (bsubst X T2 (BindTVar k))...
        apply_ih_map_bind H1 ; auto. constructor... }
    Qed.

    Lemma bsubst_ok_env :
      forall G1 G2 X T2 k,
        G1 |= T2 ~:: k ->
        ok_env (G1 & X ~ BindTVar k & G2) ->
        ok_env (G1 & map (bsubst X T2) G2).
    Proof with eauto using ok_data_bsubst, ok_kind_bsubst, ok_type_lct,
        ok_data_tvar_strengthening, ok_kind_tvar_strengthening with mcore.
      introv Htk Henv.
      induction G2 using env_ind.
      { Case "Empty". autorewrite with rew_env_map rew_env_concat in *.
        apply* ok_env_push. }
      { Case "Push". autorewrite with rew_env_map rew_env_concat in *.
        specializes IHG2 (ok_env_push _ _ _ Henv).
        lets [? Hdisj] : ok_push_inv (ok_env_ok _ Henv).
        destruct v.
        { SCase "BindTName". constructor~. }
        { SCase "BindCon". forwards (L & T' & Heq & Hd & Htk' & HT): ok_env_con_inv Henv.
          substs. apply_fresh EnvCon as K...
          - replaces (BindTVar (KiData d)) with (bsubst X T2 (BindTVar (KiData d))) ; auto.
            rewrite tsubst_topen_comm...
            apply_ih_map_bind ok_type_tsubst ; try rewrite* concat_assoc ; auto.
            constructor~. constructor...
          - binds_cases HT ; auto.
            replaces BindTName with (bsubst X T2 BindTName) ; auto. }
        { SCase "BindTVar". forwards Hk: ok_env_tvar_inv Henv. constructor... }
        { SCase "BindVar". forwards Htk': ok_env_var_inv Henv.
          constructor~. applys* ok_type_tsubst Htk'. }
        (* { SCase "BindMatch". constructor~. } *)
      }
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
        X \notin tfv T.
    Proof.
      introv Htk Hfresh.
      induction Htk; simpls*.
      { Case "TyFVar". intros contra.
        rewrite in_singleton in contra. substs.
        apply get_none in Hfresh.
        apply binds_get in H0.
        fequals. }
      { Case "TyAll". pick_fresh Y.
        forwards~ Htk: H1 Y.
        forwards~ Hnin1 : topen_notin Htk. }
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
          apply ok_env_con_inv in Henv as (? & ? & ? & ? & Htk & ?).
          pick_fresh X'. forwards~ Hnin : ok_type_notin X (Htk X').
          applys~ topen_notin Hnin. }
        { SCase "BindVar".
          apply ok_env_var_inv in Henv.
          apply* ok_type_notin. } }
    Qed.

    Lemma ok_term_tsubst :
      forall G2 G1 t k T1 T2 X,
        G1 & X ~ BindTVar k & G2 |= t ~: T1 ->
        G1 |= T2 ~:: k ->
        G1 & map (bsubst X T2) G2 |= [{X => T2}]t ~: ({X => T2}T1).
    Proof with eauto using ok_env_strengthening, bsubst_ok_env, ok_type_lct with mcore.
      introv hasType Henv.
      remember (G1 & X ~ BindTVar k & G2) as G. gen G2.
      induction hasType; intros; simpls; substs...
      { Case "TmFVar". constructor...
        replaces (BindVar ({X => T2} ty)) with (bsubst X T2 (BindVar ty))...
        binds_cases H0 ; auto.
        assert (X # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
        rewrite* (env_bsubst_fresh G1 X T2). }
      { Case "TmLam". apply_fresh* TLam as x.
        + applys ok_type_tsubst...
        + replaces (BindVar ({X => T2}ty1)) with (bsubst X T2 (BindVar ty1))...
          rewrite tsubst_t_open_comm. apply_ih_map_bind H1 ; auto. }
      { Case "TmTyLam". apply_fresh* TTyLam.
        + apply ok_kind_bsubst. apply* ok_kind_tvar_strengthening.
        + replaces (BindTVar k0) with (bsubst X T2 (BindTVar k0))...
          rewrite tsubst_topen_comm... rewrite topen_t_tsubst_comm...
          apply_ih_map_bind H1 ; auto. }
      { Case "TmTyApp".
        rewrite tsubst_topen_distr... constructors*.
        apply* ok_type_tsubst. }
      { Case "TmCon".
        apply TCon with (d := d) (ty1 := {X => T2}ty1) ; try apply* ok_type_tsubst.
        - replaces (BindCon d ({X => T2} ty1) (FTName T)) with (bsubst X T2 (BindCon d ty1 (FTName T)))...
          binds_cases H ; auto.
          assert (X # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite* (env_bsubst_fresh G1 X T2).
        - rewrite <- tsubst_topen_distr... }
      { Case "TmType". apply_fresh TType.
        - apply tsubst_lct...
        - replaces BindTName with (bsubst X T2 BindTName)...
          rewrite Topen_t_tsubst_comm... apply_ih_map_bind H1 ; auto. }
      { Case "TmConDef".
        apply_fresh TConDef.
        - apply* ok_data_bsubst. apply* ok_data_tvar_strengthening.
        - replaces (BindTVar (KiData d)) with (bsubst X T2 (BindTVar (KiData d)))...
          rewrite tsubst_topen_comm...
          apply_ih_map_bind ok_type_tsubst ; eauto ; try rewrite* concat_assoc.
          apply_ih_map_bind bsubst_ok_env ; eauto ; try rewrite* concat_assoc.
        - binds_cases H1 ; auto.
          replaces BindTName with (bsubst X T2 BindTName) ; auto.
        - apply tsubst_lct...
        - replaces (BindCon d ({X => T2} ty1) (FTName T)) with (bsubst X T2 (BindCon d ty1 (FTName T)))...
          rewrite Kopen_t_tsubst_comm... apply_ih_map_bind H4 ; auto. }
    Qed.

    Lemma ok_data_comm :
      forall G2 G1 x1 x2 b1 b2 d,
        ok_data (G1 & x1 ~ b1 & x2 ~ b2 & G2) d ->
        ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
        ok_data (G1 & x2 ~ b2 & x1 ~ b1 & G2) d.
    Proof.
      introv Hd Henv. remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma.
      induction Hd ; substs ; constructor~.
      - binds_cases H0 ; auto.
        apply* binds_concat_left_ok. apply* binds_concat_left_ok.
        applys* ok_concat_inv_l G2.
      - induction* Ks. inverts H1.
        constructors~. binds_cases H8 ; eauto.
        apply* binds_concat_left_ok. apply* binds_concat_left_ok.
        applys* ok_concat_inv_l G2.
    Qed.

    Lemma ok_kind_comm :
      forall G2 G1 x1 x2 b1 b2 k,
        ok_kind (G1 & x1 ~ b1 & x2 ~ b2 & G2) k ->
        ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
        ok_kind (G1 & x2 ~ b2 & x1 ~ b1 & G2) k.
    Proof with eauto using ok_data_comm with mcore.
      introv Hk Henv.
      remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma.
      induction Hk ; substs...
    Qed.

    Lemma ok_type_comm :
      forall G2 G1 x1 x2 b1 b2 ty k,
        G1 & x1 ~ b1 & x2 ~ b2 & G2 |= ty ~:: k ->
        ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
        G1 & x2 ~ b2 & x1 ~ b1 & G2 |= ty ~:: k.
    Proof with eauto using ok_data_comm, ok_kind_comm with mcore.
      introv Htk Henv.
      remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma. gen G2.
      induction Htk ; intros ; substs...
      { Case "TyFVar". constructor~. binds_cases H0 ; auto.
        apply* binds_concat_left_ok. apply* binds_concat_left_ok.
        applys* ok_concat_inv_l G2. }
      { Case "TyAll". apply_fresh KAll as X...
        apply_ih_bind H1 ; auto. constructors... }
    Qed.

    Lemma ok_term_comm :
      forall G2 G1 x1 x2 b1 b2 t ty,
        G1 & x1 ~ b1 & x2 ~ b2 & G2 |= t ~: ty ->
        ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
        G1 & x2 ~ b2 & x1 ~ b1 & G2 |= t ~: ty.
    Proof with eauto using ok_data_comm, ok_kind_comm, ok_type_comm with mcore.
      introv Htype Henv.
      remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma. gen G2.
      induction Htype ; intros ; substs...
      { Case "TmFVar". constructor~. binds_cases H0 ; auto.
        apply* binds_concat_left_ok. apply* binds_concat_left_ok.
        applys* ok_concat_inv_l G2. }
      { Case "TmLam". apply_fresh TLam as x...
        apply_ih_bind H1 ; auto. constructor... }
      { Case "TmTyLam". apply_fresh TTyLam as X...
        apply_ih_bind H1 ; auto. constructor... }
      { Case "TmCon". constructors... binds_cases H...
        apply* binds_concat_left_ok. apply* binds_concat_left_ok.
        applys* ok_concat_inv_l G2. }
      { Case "TmType". apply_fresh TType as T...
        apply_ih_bind H1 ; auto. constructor... }
      { Case "TmConDef".
        assert (binds T BindTName (G1 & x2 ~ b2 & x1 ~ b1 & G2)).
        { binds_cases H1...
          apply* binds_concat_left_ok. apply* binds_concat_left_ok.
          applys* ok_concat_inv_l G2. }
        apply_fresh TConDef as X...
        + apply_ih_bind ok_type_comm. eauto. constructor...
        + apply_ih_bind H4 ; auto. apply_fresh EnvCon as X'...
          apply_ih_bind ok_type_comm. eauto. constructor... }
    Qed.

    Lemma ok_env_binds_con_inv :
      forall Gamma K d ty T,
        ok_env Gamma  ->
        binds K (BindCon d ty T) Gamma ->
        exists L T',
          T = FTName T'
          /\ ok_data Gamma d
          /\ (forall X, X \notin L -> Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty ~:: KiType)
          /\ binds T' BindTName Gamma.
    Proof.
      introv Henv Hbinds.
      induction Gamma using env_ind.
      - false. apply* binds_empty_inv.
      - binds_cases Hbinds.
        + destruct~ IHGamma as (L & T' & Heq & Hd & Htk & Hbinds'). apply* ok_env_push.
          exists (L \u dom Gamma \u \{x}) T'. splits*. apply_empty~ ok_data_weakening.
          introv Hfresh. apply~ ok_type_weakening. constructor~. constructor.
          apply_empty~ ok_data_weakening. apply* binds_concat_left_ok.
        + inverts EQ. forwards* (L & T' & Heq & Hd & Htk & Hbinds') : ok_env_con_inv.
          exists (L \u dom Gamma \u \{K}) T'. splits~. apply_empty~ ok_data_weakening.
          introv Hfresh. apply~ ok_type_weakening. constructor~. constructor.
          apply_empty~ ok_data_weakening. apply* binds_concat_left_ok.
    Qed.

    Lemma ok_env_binds_tvar_inv :
      forall Gamma X k,
      ok_env Gamma ->
      binds X (BindTVar k) Gamma ->
      ok_kind Gamma k.
    Proof.
      introv Henv Hbinds.
      induction Gamma using env_ind.
      - false. apply* binds_empty_inv.
      - binds_cases Hbinds.
        + apply_empty~ ok_kind_weakening. apply~ IHGamma. apply* ok_env_push.
        + substs. forwards* Hk: ok_env_tvar_inv. apply_empty~ ok_kind_weakening.
    Qed.

    Lemma ok_type_ok_kind :
      forall Gamma T k,
        Gamma |= T ~:: k ->
        ok_kind Gamma k.
    Proof. introv Htk. induction* Htk. apply* ok_env_binds_tvar_inv. Qed.

    Lemma ok_data_tname_strengthening :
      forall G2 G1 T d,
        T \notin Tfv_d d ->
        ok_data (G1 & T ~ BindTName & G2) d ->
        ok_data (G1 & G2) d.
    Proof.
      introv Hfv Hd. remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma.
      unfolds Tfv_d. induction Hd ; substs ; constructor ; rew_listx~ in Hfv.
      - binds_cases H0 ; auto. notin_false.
      - induction* Ks. inverts H1.
        constructors~. binds_cases H8 ; eauto.
    Qed.

    Lemma ok_kind_tname_strengthening :
      forall T G2 G1 k,
        T \notin Tfv_k k ->
        ok_kind (G1 & T ~ BindTName & G2) k ->
        ok_kind (G1 & G2) k.
    Proof with eauto using ok_data_tname_strengthening with mcore.
      introv Hfv Hk.
      remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma.
      induction Hk ; substs...
    Qed.

    Lemma ok_type_tname_strengthening :
      forall T G2 G1 ty k,
        T \notin Tfv_ty ty ->
        G1 & T ~ BindTName & G2 |= ty ~:: k ->
        ok_env (G1 & G2) ->
        G1 & G2 |= ty ~:: k.
    Proof with eauto using ok_data_tname_strengthening, ok_kind_tname_strengthening with mcore.
      introv Hfv Htk Henv.
      remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma. gen G2.
      induction Htk ; intros ; simpls ; substs...
      { Case "TyFVar". constructor~. binds_cases H0 ; auto. }
      { Case "TyAll". rewrite notin_union in Hfv ; destruct Hfv.
        apply_fresh KAll as X...
        apply_ih_bind H1 ; auto. rewrite topen_notin_T ; simpls~. constructors... }
    Qed.

    Lemma ok_data_notin_T :
      forall Gamma d X,
        ok_data Gamma d ->
        X # Gamma ->
        X \notin Tfv_d d.
    Proof.
      introv Hd Hfresh. unfolds Tfv_d.
      induction Hd ; rew_listx~.
      rewrite notin_union. splits*.
      - rewrite notin_singleton. intro. substs.
        forwards~ Hin : get_some_inv H0.
    Qed.

    Lemma ok_kind_notin_T :
      forall Gamma k X,
        ok_kind Gamma k ->
        X # Gamma ->
        X \notin Tfv_k k.
    Proof.
      introv Hk Hfresh. unfolds Tfv_k.
      destruct~ Hk. apply* ok_data_notin_T.
    Qed.

    Lemma assoc_data_in :
      forall d T Ks,
        mem (FTName T, Ks) d -> T \in Tfv_d d.
    Proof.
      introv Hassoc. unfolds Tfv_d.
      induction Hassoc ; rew_listx~.
      - rewrite~ in_union. rewrite~ in_singleton.
      - destruct y. rewrite~ in_union.
    Qed.

    Lemma ok_type_notin_T :
      forall Gamma T k X,
        Gamma |= T ~:: k ->
        X # Gamma ->
        X \notin Tfv_ty T.
    Proof with eauto using ok_data_notin_T, ok_kind_notin_T.
      introv Htk Hfresh.
      induction Htk; simpls...
      { Case "TyAll". rewrite notin_union. splits...
        pick_fresh Y. forwards~ Htk: H1 Y.
        rewrite topen_notin_T in Htk ; simpls~. }
      { Case "TyCon". rewrite notin_union. splits~.
        forwards Hk: ok_type_ok_kind Htk.
        forwards~ Hnin : ok_kind_notin_T X Hk.
        assert (X <> T) by (intro ; substs ; apply Hnin ; applys* assoc_data_in).
        auto. }
    Qed.

    Lemma env_Tbsubst_fresh :
      forall Gamma X T,
        ok_env Gamma ->
        X # Gamma ->
        Gamma = map (Tbsubst X T) Gamma.
    Proof with eauto using ok_env_push.
      introv Henv Hfresh.
      induction Gamma using env_ind.
      { Case "Empty". rewrite~ map_empty. }
      { Case "Push". autorewrite with rew_env_map.
        rewrite <- IHGamma...
        destruct~ v ; repeat fequals ; unfold Tbsubst.
        { SCase "BindCon".
          apply ok_env_con_inv in Henv as (? & ? & ? & ? & Htk & ?). fequals.
          - rewrite~ Tsubst_d_fresh. forwards~ Hnin : ok_data_notin_T X H0.
          - rewrite~ Tsubst_ty_fresh. pick_fresh X'.
            forwards~ Hnin : ok_type_notin_T X (Htk X').
            rewrite topen_notin_T in Hnin ; simpls~.
          - destruct t0 ; solve_var. inverts H. forwards* Hin : get_some_inv x1.
            assert (Hnin: x1 # Gamma) by auto. contradiction. }
        { SCase "BindTVar".
          apply ok_env_tvar_inv in Henv. fequals.
          rewrite~ Tsubst_k_fresh. apply* ok_kind_notin_T. }
        { SCase "BindVar".
          apply ok_env_var_inv in Henv. fequals.
          rewrite~ Tsubst_ty_fresh. apply* ok_type_notin_T. } }
    Qed.

    Lemma assoc_Tsubst :
      forall T T' S Ks d,
        mem (FTName S, Ks) d ->
        mem (Tsubst T (FTName T') (FTName S), Ks) (Tsubst_d T (FTName T') d).
    Proof.
      introv Hassoc. unfolds Tsubst_d.
      induction Hassoc ; rew_listx~.
    Qed.

    Lemma assoc_Tsubst_inv :
      forall Gamma T T' S Ks d,
        ok_data Gamma d ->
        T' # Gamma ->
        T' <> S ->
        mem (Tsubst T (FTName T') (FTName S), Ks) (Tsubst_d T (FTName T') d) ->
        mem (FTName S, Ks) d.
    Proof.
      introv Hd Hfresh Hneq Hassoc. unfolds Tsubst_d.
      induction Hd ; inverts Hassoc ; rew_listx~.
      left. fequals. inverts H0.
      rewrite~ (Tsubst_inj S T0 T T'). intro Heq ; substs.
      forwards Hin : get_some_inv T0 ; eauto.
    Qed.

    Lemma ok_data_Tsubst :
      forall G2 G1 T T' d,
        ok_data (G1 & T ~ BindTName & G2) d ->
        T' # G1 & T ~ BindTName & G2 ->
        ok_env (G1 & T ~ BindTName & G2) ->
        ok_data (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2)
                (Tsubst_d T (FTName T') d).
    Proof with eauto with mcore.
      introv Hd Hfresh Henv. assert (Henv' : ok_env G1)
        by (applys ok_env_concat ; applys* ok_env_concat).
      remember (G1 & T ~ BindTName & G2). unfolds Tsubst_d.
      induction Hd; substs; rew_listx*.
      asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
      rewrite Heq. constructor~.
      - rewrite <- Heq. folds (Tsubst_d T (FTName T') d). introv contra.
        apply (assoc_Tsubst_inv (G1 & T ~ BindTName & G2)) in contra ; jauto.
        intro ; substs. forwards~ Hin : get_some_inv H0.
      - solve_var ; inverts~ Heq. binds_cases H0 ; auto.
        apply~ binds_concat_left. apply binds_concat_left_ok...
        replaces BindTName with (Tbsubst T (FTName T') BindTName)...
      - remember (FTName T0). remember (G1 & T ~ BindTName & G2).
        induction H1 ; substs.
        + constructor.
        + apply CCons with (d := Tsubst_d T (FTName T') d0)
                           (ty := Tsubst_ty T (FTName T') ty) ; auto.
          replaces (BindCon (Tsubst_d T (FTName T') d0) (Tsubst_ty T (FTName T') ty) (FTName S))
            with (Tbsubst T (FTName T') (BindCon d0 ty (FTName T0))). rewrite~ <- Heq.
          binds_cases H3 ; auto.
          apply~ binds_concat_left. apply binds_concat_left_ok...
          assert (T # G1). applys ok_push_inv...
          rewrite~ (env_Tbsubst_fresh G1 T (FTName T'))...
    Qed.

    Lemma ok_kind_Tsubst :
      forall G2 G1 T T' k,
        ok_kind (G1 & T ~ BindTName & G2) k ->
        ok_env  (G1 & T ~ BindTName & G2) ->
        T' # G1 & T ~ BindTName & G2 ->
        ok_kind (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2)
                (Tsubst_k T (FTName T') k).
    Proof.
      introv Hk. remember (G1 & T ~ BindTName & G2) as G.
      induction Hk; intros; substs; constructor.
      apply~ ok_data_Tsubst.
    Qed.

    Lemma ok_type_Tsubst :
      forall G2 G1 T T' ty k,
        G1 & T ~ BindTName & G2 |= ty ~:: k ->
        T' # G1 & T ~ BindTName & G2 ->
        ok_env  (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2) ->
        G1 & T' ~ BindTName &
          map (Tbsubst T (FTName T')) G2 |=
              Tsubst_ty T (FTName T') ty ~:: Tsubst_k T (FTName T') k.
    Proof with eauto with mcore.
      introv Htk Hfresh Henv. assert (Henv' : ok_env G1)
        by (applys ok_env_concat ; applys* ok_env_concat).
      remember (G1 & T ~ BindTName & G2) as G. gen G2.
      induction Htk; intros; substs; simpls...
      { Case "TyFVar". constructor...
        replaces (BindTVar (Tsubst_k T (FTName T') k))
          with (Tbsubst T (FTName T') (BindTVar k))... binds_cases H0 ; auto.
        apply~ binds_concat_left. apply* binds_concat_left_ok.
        assert (T # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
        rewrite~ (env_Tbsubst_fresh G1 T (FTName T')). }
      { Case "TyAll". apply_fresh KAll as X.
        + apply ok_kind_Tsubst...
        + replaces (BindTVar (Tsubst_k T (FTName T') k))
            with (Tbsubst T (FTName T') (BindTVar k))...
          rewrite <- Tsubst_ty_topen_comm. apply_ih_map_bind H1 ; auto.
          constructor~. apply~ ok_kind_Tsubst... }
      { Case "TyCon".
        asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
        simpls. rewrite Heq. apply KCon with (d := Tsubst_d T (FTName T') d) (Ks := Ks)...
        rewrite <- Heq. applys~ assoc_Tsubst. }
      { Case "TyData". constructor~. apply~ ok_data_Tsubst... }
    Qed.

    Lemma Tbsubst_ok_env :
      forall G1 G2 T T',
        ok_env (G1 & T ~ BindTName & G2) ->
        T' # G1 & T ~ BindTName & G2 ->
        ok_env (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2).
    Proof with eauto using ok_data_Tsubst, ok_kind_Tsubst, ok_type_Tsubst with mcore.
      introv Henv Hfresh. assert (Henv1 : ok_env G1)
        by (applys ok_env_concat; applys* ok_env_concat).
      induction G2 using env_ind.
      { Case "Empty". autorewrite with rew_env_map rew_env_concat in *.
        constructor~. }
      { Case "Push". autorewrite with rew_env_map rew_env_concat in *.
        specializes IHG2 (ok_env_push _ _ _ Henv).
        lets [? Hdisj] : ok_push_inv (ok_env_ok _ Henv).
        assert (ok_env (G1 & T ~ BindTName & G2)) by apply* ok_env_concat.
        destruct v.
        { SCase "BindTName". constructor~. }
        { SCase "BindCon". forwards (L & T0 & Heq & Hd & Htk' & HT): ok_env_con_inv Henv.
          substs. asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
          simpls. rewrite Heq. apply_fresh EnvCon as X...
          - replaces (BindTVar (KiData (Tsubst_d T (FTName T') d)))
              with (Tbsubst T (FTName T') (BindTVar (KiData d))) ; auto.
            replaces KiType with (Tsubst_k T (FTName T') KiType) ; auto.
            rewrite <- Tsubst_ty_topen_comm.
            apply_ih_map_bind ok_type_Tsubst ; try rewrite* concat_assoc ; auto.
            constructor...
          - solve_var ; inverts~ Heq. binds_cases HT ; auto.
            apply~ binds_concat_left. apply* binds_concat_left_ok.
            replaces BindTName with (Tbsubst T (FTName T') BindTName) ; eauto. }
        { SCase "BindTVar". forwards Hk: ok_env_tvar_inv Henv. constructor... }
        { SCase "BindVar". forwards Htk': ok_env_var_inv Henv. constructor~.
          replaces KiType with (Tsubst_k T (FTName T') KiType)... }
        (* { SCase "BindMatch". constructor~. } *)
      }
    Qed.

    Lemma ok_term_Tsubst :
      forall G2 G1 T T' t ty,
        G1 & T ~ BindTName & G2 |= t ~: ty ->
        T' # G1 & T ~ BindTName & G2 ->
        G1 & T' ~ BindTName &
          map (Tbsubst T (FTName T')) G2 |=
              Tsubst_t T (FTName T') t ~: Tsubst_ty T (FTName T') ty.
    Proof with eauto using Tbsubst_ok_env with mcore.
      introv Htype. assert (Henv : ok_env G1)
        by (applys ok_env_concat ; applys* ok_env_concat).
      remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma. gen G2.
      induction Htype ; intros ; substs...
      { Case "TmFVar". constructor...
        replaces (BindVar (Tsubst_ty T (FTName T') ty))
          with (Tbsubst T (FTName T') (BindVar ty))... binds_cases H0 ; auto.
        apply~ binds_concat_left. apply* binds_concat_left_ok.
        assert (T # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
        rewrite~ (env_Tbsubst_fresh G1 T (FTName T')). }
      { Case "TmLam". apply_fresh TLam as x.
        + replaces KiType with (Tsubst_k T (FTName T') KiType)...
          apply ok_type_Tsubst...
        + rewrite <- Tsubst_t_open_comm. folds (Tsubst_ty T (FTName T') ty1).
          replaces (BindVar (Tsubst_ty T (FTName T') ty1))
            with (Tbsubst T (FTName T') (BindVar ty1))...
          apply_ih_map_bind H1 ; auto. }
      { Case "TmTyLam". apply_fresh TTyLam as X.
        + apply ok_kind_Tsubst...
        + rewrite <- Tsubst_t_topen_comm. rewrite <- Tsubst_ty_topen_comm.
          replaces (BindTVar (Tsubst_k T (FTName T') k))
            with (Tbsubst T (FTName T') (BindTVar k))...
          apply_ih_map_bind H1 ; auto. }
      { Case "TmTyApp". rewrite Tsubst_ty_topen_distr. constructors*.
        apply ok_type_Tsubst... }
      { Case "TmCon".
        asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
        simpls. rewrite Heq.
        apply TCon with (d := Tsubst_d T (FTName T') d) (ty1 := Tsubst_ty T (FTName T') ty1).
        - replaces (BindCon (Tsubst_d T (FTName T') d) (Tsubst_ty T (FTName T') ty1) (FTName S))
            with (Tbsubst T (FTName T') (BindCon d ty1 (FTName T0))). rewrite~ <- Heq.
          binds_cases H ; auto.
          apply~ binds_concat_left. apply* binds_concat_left_ok.
          assert (T # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite~ (env_Tbsubst_fresh G1 T (FTName T')).
        - replaces (KiData (Tsubst_d T (FTName T') d)) with (Tsubst_k T (FTName T') (KiData d))...
          apply* ok_type_Tsubst.
        - replaces (KiData [(FTName S, FCon K :: [])])
            with (Tsubst_k T (FTName T') (KiData [(FTName T0, FCon K :: [])])). rewrite~ <- Heq.
          apply* ok_type_Tsubst.
        - rewrite <- Tsubst_ty_topen_distr... }
      { Case "TmType". apply_fresh TType as T0.
        + apply~ Tsubst_ty_lct.
        + replaces BindTName with (Tbsubst T (FTName T') BindTName)...
          rewrite~ Tsubst_t_Topen_comm. apply_ih_map_bind H1 ; auto. }
      { Case "TmConDef".
        asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
        simpls. rewrite Heq. apply_fresh TConDef as X.
        - apply ok_data_Tsubst...
        - replaces KiType with (Tsubst_k T (FTName T') KiType)...
          replaces (BindTVar (KiData (Tsubst_d T (FTName T') d)))
            with (Tbsubst T (FTName T') (BindTVar (KiData d)))...
          rewrite <- Tsubst_ty_topen_comm.
          apply_ih_map_bind ok_type_Tsubst ; eauto ; try rewrite* concat_assoc.
          constructor... apply ok_kind_Tsubst...
        - solve_var ; inverts~ Heq.
          binds_cases H1 ; auto.
          apply~ binds_concat_left. apply binds_concat_left_ok...
          replaces BindTName with (Tbsubst T (FTName T') BindTName)...
        - apply~ Tsubst_ty_lct.
        - replaces (BindCon (Tsubst_d T (FTName T') d) (Tsubst_ty T (FTName T') ty1) (FTName S))
            with (Tbsubst T (FTName T') (BindCon d ty1 (FTName T0))). rewrite~ <- Heq.
          rewrite Tsubst_t_Kopen_comm. apply_ih_map_bind H4 ; auto. }
    Qed.

    Lemma ok_data_con_strengthening :
      forall K G2 G1 d' ty' T d,
        K \notin Kfv_d d ->
        ok_data (G1 & K ~ BindCon d' ty' T & G2) d ->
        ok_data (G1 & G2) d.
    Proof.
      introv Hfv Hd. remember (G1 & K ~ BindCon d' ty' T & G2) as Gamma eqn:HGamma.
      unfolds Kfv_d. induction Hd ; substs ; constructor ; rew_listx~ in Hfv.
      - binds_cases H0 ; auto.
      - induction* Ks. inverts H1. rew_listx~ in Hfv.
        constructors~. binds_cases H8 ; eauto. notin_false.
    Qed.

    Lemma ok_kind_con_strengthening :
      forall K G2 G1 d ty' T k,
        K \notin Kfv_k k ->
        ok_kind (G1 & K ~ BindCon d ty' T & G2) k ->
        ok_kind (G1 & G2) k.
    Proof with eauto using ok_data_con_strengthening with mcore.
      introv Hfv Hk.
      remember (G1 & K ~ BindCon d ty' T & G2) as Gamma eqn:HGamma.
      induction Hk ; substs...
    Qed.

    Lemma ok_type_con_strengthening :
      forall K G2 G1 d ty' T ty k,
        K \notin Kfv_ty ty ->
        G1 & K ~ BindCon d ty' T & G2 |= ty ~:: k ->
        ok_env (G1 & G2) ->
        G1 & G2 |= ty ~:: k.
    Proof with eauto using ok_data_con_strengthening, ok_kind_con_strengthening with mcore.
      introv Hfv Htk Henv.
      remember (G1 & K ~ BindCon d ty' T & G2) as Gamma eqn:HGamma. gen G2.
      induction Htk ; intros ; simpls ; substs...
      { Case "TyFVar". constructor~. binds_cases H0 ; auto. }
      { Case "TyAll". rewrite notin_union in Hfv ; destruct Hfv.
        apply_fresh KAll as X...
        apply_ih_bind H1 ; auto. rewrite topen_notin_K ; simpls~. constructors... }
    Qed.

    Lemma ok_data_notin_K :
      forall Gamma d X,
        ok_data Gamma d ->
        X # Gamma ->
        X \notin Kfv_d d.
    Proof.
      introv Hd Hfresh. unfolds Kfv_d.
      induction Hd ; rew_listx~.
      rewrite notin_union. splits*.
      induction H1 ; rew_listx~ ; rewrite notin_union ; splits~.
      - rewrite notin_singleton. intro. substs.
        forwards~ Hin : get_some_inv H3.
    Qed.

    Lemma ok_kind_notin_K :
      forall Gamma k X,
        ok_kind Gamma k ->
        X # Gamma ->
        X \notin Kfv_k k.
    Proof.
      introv Hk Hfresh. unfolds Kfv_k.
      destruct~ Hk. apply* ok_data_notin_K.
    Qed.

    Lemma ok_type_notin_K :
      forall Gamma T k X,
        Gamma |= T ~:: k ->
        X # Gamma ->
        X \notin Kfv_ty T.
    Proof with eauto using ok_data_notin_K, ok_kind_notin_K.
      introv Htk Hfresh.
      induction Htk; simpls...
      { Case "TyAll". rewrite notin_union. splits...
        pick_fresh Y. forwards~ Htk: H1 Y.
        rewrite topen_notin_K in Htk ; simpls~. }
    Qed.

    Lemma env_Kbsubst_fresh :
      forall Gamma X K,
        ok_env Gamma ->
        X # Gamma ->
        Gamma = map (Kbsubst X K) Gamma.
    Proof with eauto using ok_env_push.
      introv Henv Hfresh.
      induction Gamma using env_ind.
      { Case "Empty". rewrite~ map_empty. }
      { Case "Push". autorewrite with rew_env_map.
        rewrite <- IHGamma...
        destruct~ v ; repeat fequals ; unfold Kbsubst.
        { SCase "BindCon".
          apply ok_env_con_inv in Henv as (? & ? & ? & ? & Htk & ?). fequals.
          - rewrite~ Ksubst_d_fresh. forwards~ Hnin : ok_data_notin_K X H0.
          - rewrite~ Ksubst_ty_fresh. pick_fresh X'.
            forwards~ Hnin : ok_type_notin_K X (Htk X').
            rewrite topen_notin_K in Hnin ; simpls~. }
        { SCase "BindTVar".
          apply ok_env_tvar_inv in Henv. fequals.
          rewrite~ Ksubst_k_fresh. apply* ok_kind_notin_K. }
        { SCase "BindVar".
          apply ok_env_var_inv in Henv. fequals.
          rewrite~ Ksubst_ty_fresh. apply* ok_type_notin_K. } }
    Qed.

    Lemma assoc_Ksubst :
      forall K K' S Ks d,
        mem (FTName S, Ks) d ->
        mem (FTName S, LibList.map (Ksubst K (FCon K')) Ks) (Ksubst_d K (FCon K') d).
    Proof.
      introv Hassoc. unfolds Ksubst_d.
      induction Hassoc ; rew_listx~.
    Qed.

    Lemma assoc_Ksubst_inv :
      forall K K' S Ks d,
        mem (FTName S, Ks) (Ksubst_d K (FCon K') d) ->
        exists Ks', LibList.mem (FTName S, Ks') d.
    Proof.
      introv Hassoc. unfolds Ksubst_d.
      induction d ; inverts Hassoc ; destruct a ; rew_listx in *.
      - inverts H0. exists~.
      - inverts H. destruct~ IHd as (Ks'&?). exists~ Ks'.
    Qed.

    Lemma mem_Ksubst_inv :
      forall Gamma K K' S Ks T,
        ok_cons Gamma Ks T ->
        K' # Gamma ->
        K' <> S ->
        mem (Ksubst K (FCon K') (FCon S)) (LibList.map (Ksubst K (FCon K')) Ks) ->
        mem (FCon S) Ks.
    Proof.
      introv HKs Hfresh Hneq Hmem.
      induction HKs ; inverts Hmem ; rew_listx~ in *.
      left. fequals.
      rewrite~ (Ksubst_inj S K0 K K'). intro Heq ; substs.
      forwards Hin : get_some_inv H0 ; eauto.
    Qed.

    Lemma ok_data_Ksubst :
      forall G2 G1 K K' d' ty' T d,
        ok_data (G1 & K ~ BindCon d' ty' T & G2) d ->
        K' # G1 & K ~ BindCon d' ty' T & G2 ->
        ok_env (G1 & K ~ BindCon d' ty' T & G2) ->
        ok_data (G1 & K' ~ BindCon d' ty' T & map (Kbsubst K (FCon K')) G2)
                (Ksubst_d K (FCon K') d).
    Proof with eauto with mcore.
      introv Hd Hfresh Henv. assert (Henv' : ok_env G1)
        by (applys ok_env_concat ; applys* ok_env_concat).
      remember (G1 & K ~ BindCon d' ty' T & G2). unfolds Ksubst_d.
      induction Hd; substs; rew_listx*. constructor~.
      - introv contra. forwards* (Ks'&Hassoc): assoc_Ksubst_inv.
      - binds_cases H0 ; auto.
        apply~ binds_concat_left. apply binds_concat_left_ok...
        replaces BindTName with (Kbsubst K (FCon K') BindTName)...
      - remember (G1 & K ~ BindCon d' ty' T & G2).
        induction H1 ; substs.
        + constructor.
        + asserts (S, Heq): (lcK (Ksubst K (FCon K') (FCon K0))). solve_var.
          rew_listx. rewrite Heq.
          apply CCons with (d := Ksubst_d K (FCon K') d0)
                           (ty := Ksubst_ty K (FCon K') ty) ; auto.
          * rewrite <- Heq. intro contra.
            apply H2. applys* mem_Ksubst_inv contra. intro ; subst.
            forwards~ ?: get_some_inv H3.
          * assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
            solve_var ; inverts Heq.
            ** forwards* Heqbind : binds_middle_eq_inv H3. inverts Heqbind.
               forwards (?&?&?&Hd'&Htk&?): ok_env_con_inv G1 K0 d' ty' T. applys~ ok_env_concat G2.
               pick_fresh X. forwards~ Hnin: ok_type_notin_K K0 (Htk X).
               rewrite topen_notin_K in Hnin ; simpls~. forwards~ Hnin': ok_data_notin_K K0 Hd'.
               rewrite~ Ksubst_d_fresh. rewrite~ Ksubst_ty_fresh.
            ** replaces (BindCon (Ksubst_d K (FCon K') d0) (Ksubst_ty K (FCon K') ty) T1)
                 with (Kbsubst K (FCon K') (BindCon d0 ty T1))...
               binds_cases H3 ; auto.
               apply~ binds_concat_left. apply binds_concat_left_ok...
               rewrite~ (env_Kbsubst_fresh G1 K (FCon K'))...
    Qed.

    Lemma ok_kind_Ksubst :
      forall G2 G1 K K' d ty' T k,
        ok_kind (G1 & K ~ BindCon d ty' T & G2) k ->
        ok_env  (G1 & K ~ BindCon d ty' T & G2) ->
        K' # G1 & K ~ BindCon d ty' T & G2 ->
        ok_kind (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2)
                (Ksubst_k K (FCon K') k).
    Proof.
      introv Hk. remember (G1 & K ~ BindCon d ty' T & G2) as G.
      induction Hk; intros; substs; constructor.
      apply~ ok_data_Ksubst.
    Qed.

    Lemma ok_type_Ksubst :
      forall G2 G1 K K' d ty' T ty k,
        G1 & K ~ BindCon d ty' T & G2 |= ty ~:: k ->
        ok_env (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2) ->
        K' # G1 & K ~ BindCon d ty' T & G2 ->
        G1 & K' ~ BindCon d ty' T &
          map (Kbsubst K (FCon K')) G2 |=
              Ksubst_ty K (FCon K') ty ~:: Ksubst_k K (FCon K') k.
    Proof with eauto with mcore.
      introv Htk Hfresh Henv. assert (Henv' : ok_env G1)
        by (applys ok_env_concat ; applys* ok_env_concat).
      remember (G1 & K ~ BindCon d ty' T & G2). gen G2.
      induction Htk; intros; substs; simpls...
      { Case "TyFVar". constructor...
        replaces (BindTVar (Ksubst_k K (FCon K') k))
          with (Kbsubst K (FCon K') (BindTVar k))... binds_cases H0 ; auto.
        apply~ binds_concat_left. apply* binds_concat_left_ok.
        assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
        rewrite~ (env_Kbsubst_fresh G1 K (FCon K')). }
      { Case "TyAll". apply_fresh KAll as X.
        + apply ok_kind_Ksubst...
        + replaces (BindTVar (Ksubst_k K (FCon K') k))
            with (Kbsubst K (FCon K') (BindTVar k))...
          rewrite <- Ksubst_ty_topen_comm. apply_ih_map_bind H1 ; auto.
          constructor... apply ok_kind_Ksubst... }
      { Case "TyCon".
        apply KCon with (d := Ksubst_d K (FCon K') d0) (Ks := LibList.map (Ksubst K (FCon K')) Ks)...
        apply~ assoc_Ksubst. }
      { Case "TyData". constructor~. apply~ ok_data_Ksubst. }
    Qed.

    Lemma Kbsubst_ok_env :
      forall G1 G2 K K' d ty T,
        ok_env (G1 & K ~ BindCon d ty T & G2) ->
        K' # G1 & K ~ BindCon d ty T & G2 ->
        ok_env (G1 & K' ~ BindCon d ty T & map (Kbsubst K (FCon K')) G2).
    Proof with eauto using ok_data_Ksubst, ok_kind_Ksubst, ok_type_Ksubst with mcore.
      introv Henv Hfresh. assert (Henv1 : ok_env G1)
        by (applys ok_env_concat; applys* ok_env_concat).
      forwards Henv': ok_env_concat Henv. forwards (?&?&?&?&?&?): ok_env_con_inv Henv'.
      substs. induction G2 using env_ind.
      { Case "Empty". autorewrite with rew_env_map rew_env_concat in *.
        apply_fresh EnvCon... }
      { Case "Push". autorewrite with rew_env_map rew_env_concat in *.
        specializes IHG2 (ok_env_push _ _ _ Henv) ; auto.
        lets [? Hdisj] : ok_push_inv (ok_env_ok _ Henv).
        assert (ok_env (G1 & K ~ BindCon d ty (FTName x0) & G2)) by apply* ok_env_concat.
        destruct v.
        { SCase "BindTName". constructor~. }
        { SCase "BindCon". forwards (L & T0 & Heq & Hd & Htk' & HT): ok_env_con_inv Henv.
          substs. apply_fresh EnvCon as X...
          - replaces (BindTVar (KiData (Ksubst_d K (FCon K') d0)))
              with (Kbsubst K (FCon K') (BindTVar (KiData d0))) ; auto.
            replaces KiType with (Ksubst_k K (FCon K') KiType) ; auto.
            rewrite <- Ksubst_ty_topen_comm.
            apply_ih_map_bind ok_type_Ksubst ; try rewrite* concat_assoc ; auto.
            constructor...
          - binds_cases HT ; auto.
            apply~ binds_concat_left. apply* binds_concat_left_ok.
            replaces BindTName with (Kbsubst K (FCon K') BindTName) ; eauto. }
        { SCase "BindTVar". forwards Hk: ok_env_tvar_inv Henv. constructor... }
        { SCase "BindVar". forwards Htk': ok_env_var_inv Henv. constructor~.
          replaces KiType with (Ksubst_k K (FCon K') KiType)... }
        (* { SCase "BindMatch". constructor~. } *)
      }
    Qed.

    Lemma ok_term_Ksubst :
      forall G2 G1 K K' d ty' T t ty,
        G1 & K ~ BindCon d ty' T & G2 |= t ~: ty ->
        K' # G1 & K ~ BindCon d ty' T & G2 ->
        G1 & K' ~ BindCon d ty' T &
          map (Kbsubst K (FCon K')) G2 |=
              Ksubst_t K (FCon K') t ~: Ksubst_ty K (FCon K') ty.
    Proof with eauto using Kbsubst_ok_env with mcore.
      introv Htype. assert (Henv : ok_env G1)
        by (applys ok_env_concat ; applys* ok_env_concat).
      remember (G1 & K ~ BindCon d ty' T & G2). gen G2.
      induction Htype ; intros ; substs...
      { Case "TmFVar". constructor...
        replaces (BindVar (Ksubst_ty K (FCon K') ty))
          with (Kbsubst K (FCon K') (BindVar ty))... binds_cases H0 ; auto.
        apply~ binds_concat_left. apply* binds_concat_left_ok.
        assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
        rewrite~ (env_Kbsubst_fresh G1 K (FCon K')). }
      { Case "TmLam". apply_fresh TLam as x.
        + replaces KiType with (Ksubst_k K (FCon K') KiType)...
          apply ok_type_Ksubst...
        + rewrite <- Ksubst_t_open_comm. folds (Ksubst_ty K (FCon K') ty1).
          replaces (BindVar (Ksubst_ty K (FCon K') ty1))
            with (Kbsubst K (FCon K') (BindVar ty1))...
          apply_ih_map_bind H1 ; auto. }
      { Case "TmTyLam". apply_fresh TTyLam as X.
        + apply ok_kind_Ksubst...
        + rewrite <- Ksubst_t_topen_comm. rewrite <- Ksubst_ty_topen_comm.
          replaces (BindTVar (Ksubst_k K (FCon K') k))
            with (Kbsubst K (FCon K') (BindTVar k))...
          apply_ih_map_bind H1 ; auto. }
      { Case "TmTyApp". rewrite Ksubst_ty_topen_distr. constructors*.
        apply ok_type_Ksubst... }
      { Case "TmCon".
        asserts (S, Heq): (lcK (Ksubst K (FCon K') (FCon K0))). solve_var.
        simpls. rewrite Heq.
        apply TCon with (d := Ksubst_d K (FCon K') d0) (ty1 := Ksubst_ty K (FCon K') ty1).
        - assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          solve_var ; inverts Heq.
          + forwards* Heqbind : binds_middle_eq_inv H. inverts Heqbind.
            forwards (?&?&?&Hd&Htk&?): ok_env_con_inv G1 S d ty'. apply* ok_env_concat.
            pick_fresh X. forwards~ Hnin: ok_type_notin_K K0 (Htk X).
            rewrite topen_notin_K in Hnin ; simpls~. forwards~ Hnin': ok_data_notin_K K0 Hd.
            rewrite~ Ksubst_d_fresh. rewrite~ Ksubst_ty_fresh.
          + replaces (BindCon (Ksubst_d K (FCon K') d0) (Ksubst_ty K (FCon K') ty1) (FTName T0))
              with (Kbsubst K (FCon K') (BindCon d0 ty1 (FTName T0)))...
            binds_cases H ; auto.
            apply~ binds_concat_left. apply* binds_concat_left_ok.
            rewrite~ (env_Kbsubst_fresh G1 K (FCon K')).
        - replaces (KiData (Ksubst_d K (FCon K') d0)) with (Ksubst_k K (FCon K') (KiData d0))...
          apply* ok_type_Ksubst.
        - replaces (KiData [(FTName T0, FCon S :: [])])
            with (Ksubst_k K (FCon K') (KiData [(FTName T0, FCon K0 :: [])])). rewrite~ <- Heq.
          apply* ok_type_Ksubst.
        - rewrite <- Ksubst_ty_topen_distr... }
      { Case "TmType". apply_fresh TType as T0.
        + apply~ Ksubst_ty_lct.
        + replaces BindTName with (Kbsubst K (FCon K') BindTName)...
          rewrite~ Ksubst_t_Topen_comm. apply_ih_map_bind H1 ; auto. }
      { Case "TmConDef". apply_fresh TConDef as X.
        - apply~ ok_data_Ksubst...
        - replaces KiType with (Ksubst_k K (FCon K') KiType)...
          replaces (BindTVar (KiData (Ksubst_d K (FCon K') d0)))
            with (Kbsubst K (FCon K') (BindTVar (KiData d0)))...
          rewrite <- Ksubst_ty_topen_comm.
          apply_ih_map_bind ok_type_Ksubst ; eauto ; try rewrite* concat_assoc.
          constructor... apply ok_kind_Ksubst...
        - binds_cases H1 ; auto.
          apply~ binds_concat_left. apply binds_concat_left_ok...
          replaces BindTName with (Kbsubst K (FCon K') BindTName)...
        - apply~ Ksubst_ty_lct.
        - replaces (BindCon (Ksubst_d K (FCon K') d0) (Ksubst_ty K (FCon K') ty1) (FTName T0))
            with (Kbsubst K (FCon K') (BindCon d0 ty1 (FTName T0)))...
          rewrite~ Ksubst_t_Kopen_comm. apply_ih_map_bind H4 ; auto. }
    Qed.

  End Typing.
End Typing.
