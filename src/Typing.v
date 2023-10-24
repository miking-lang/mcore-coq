From TLC Require Import LibString LibList LibSet LibMap.
From MCore Require Import Syntax Ctx Tactics.
Import LibListNotation.

Open Scope liblist_scope.

Module Typing (P : PAT).
  Module C := Ctx P.
  Export C.

  Module Type PATCHECK.
    Parameter ok_pat : ctx -> pat -> type -> ctx -> Prop.
    Parameter matches_contradictory : ctx -> Prop.
    Parameter pats_compatible : list pat -> type -> Prop.
    Parameter pats_exhaustive : list pat -> type -> Prop.
  End PATCHECK.

  Module Typing (PC : PATCHECK).
    Export PC.

    (*********************************)
    (** TYPING RELATION DEFINITIONS **)
    (*********************************)

    Definition ok_data (Gamma : ctx) (d : data) : Prop :=
      forall T cons,
        binds d T cons ->
        in_ctx T BindTName Gamma /\
          forall K,
            K \in cons -> exists d ty, in_ctx K (BindCon d ty T) Gamma
    .

    Inductive ok_kind : ctx -> kind -> Prop :=
    | TypeOk : forall Gamma,
        ok_kind Gamma KiType
    (* | DataOk : forall {Gamma : ctx} {d : data}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_kind Gamma (KiData d) *)
    .
    #[export]
     Hint Constructors ok_kind : mcore.

    Reserved Notation "Gamma |= T ~:: k " (at level 50).
    Inductive ok_type : ctx -> type -> kind -> Prop :=
    | KVar : forall Gamma tv k,
        ok_ctx Gamma ->
        in_ctx tv (BindTVar k) Gamma ->
        Gamma |= TyFVar tv ~:: k
    | KArr : forall Gamma ty1 ty2,
        Gamma |= ty1 ~:: KiType ->
        Gamma |= ty2 ~:: KiType ->
        Gamma |= TyArr ty1 ty2 ~:: KiType
    | KAll : forall X Gamma k ty,
        X = length Gamma ->
        ok_kind Gamma k ->
        Gamma & BindTVar k |= {0 ~> TyFVar X} ty ~:: KiType ->
        Gamma |= TyAll k ty ~:: KiType
    (* | TyProd' : forall {Gamma : ctx} {ty1 ty2 : type}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_type Gamma (TyProd ty1 ty2) KiType *)
    (* | TyCon' : forall {Gamma : ctx} {ty : type} {d : data} {T : tname}, *)
    (*     ok_type Gamma ty (KiData d) -> *)
    (*     T \indom d -> *)
    (*     ok_type Gamma (TyCon ty T) KiType *)
    (* | TySem' : forall {Gamma : ctx} {ty1 ty2 : type} {ps : list pat}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_type Gamma (TySem ty1 ty2 ps) KiType *)
    (* | TyData' : forall {Gamma : ctx} {d : data}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_type Gamma (TyData d) (KiData d) *)
    (* | TyDataSub' : forall {Gamma : ctx} {ty : type} {d1 d2 : data}, *)
    (*     ok_type Gamma ty (KiData d1) -> *)
    (*     d2 \c d1 -> *)
    (*     (forall {T : tname}, d2[T] \c d1[T]) -> *)
    (*     ok_type Gamma ty (KiData d2) *)
    where " Gamma |= T ~:: k " := (ok_type Gamma T k)

    with ok_ctx : ctx -> Prop :=
    | CtxEmpty : ok_ctx empty
    | CtxTName : forall Gamma, ok_ctx Gamma -> ok_ctx (Gamma & BindTName)
    | CtxCon   :
      forall Gamma d ty T,
        ok_ctx Gamma ->
        ok_data Gamma d ->
        Gamma |= ty ~:: KiType ->
        in_ctx T BindTName Gamma ->
        ok_ctx (Gamma & BindCon d ty T)
    | CtxTVar : forall Gamma k,
        ok_ctx Gamma ->
        ok_kind Gamma k ->
        ok_ctx (Gamma & BindTVar k)
    | CtxVar : forall Gamma ty,
        ok_ctx Gamma ->
        Gamma |= ty ~:: KiType ->
        ok_ctx (Gamma & BindVar ty)
    | CtxSkip : forall Gamma,
        ok_ctx Gamma ->
        ok_ctx (Gamma & Skip)
    (* | CtxMatch : forall Gamma m, *)
    (*     ok_ctx Gamma -> *)
    (*     ok_ctx (Gamma & BindMatch m) *)
    .
    #[export]
     Hint Constructors ok_type : mcore.
    #[export]
     Hint Constructors ok_ctx : mcore.

    Reserved Notation "Gamma |= t ~: T " (at level 50).
    Inductive ok_term : ctx -> term -> type -> Prop :=
    | TVar : forall Gamma x ty,
        ok_ctx Gamma ->
        in_ctx x (BindVar ty) Gamma ->
        Gamma |= TmFVar x ~: ty
    | TLam : forall x Gamma ty1 ty2 t,
        x = length Gamma ->
        fresh x t ->
        Gamma |= ty1 ~:: KiType ->
        Gamma & BindVar ty1 |= [0 ~> TmFVar x]t ~: ty2 ->
        Gamma |= TmLam ty1 t ~: TyArr ty1 ty2
    | TApp : forall Gamma ty1 ty2 t1 t2,
        Gamma |= t1 ~: TyArr ty1 ty2 ->
        Gamma |= t2 ~: ty1 ->
        Gamma |= TmApp t1 t2 ~: ty2
    | TTyLam : forall X Gamma k ty t,
        X = length Gamma ->
        tfresh_t X t -> tfresh X ty ->
        ok_kind Gamma k ->
        Gamma & BindTVar k |= [{0 ~> TyFVar X}]t ~: ({0 ~> TyFVar X}ty) ->
        Gamma |= TmTyLam k t ~: (TyAll k ty)
    | TTyApp : forall Gamma k ty1 ty2 t,
        Gamma |= t ~: TyAll k ty1 ->
        Gamma |= ty2 ~:: k ->
        Gamma |= TmTyApp t ty2 ~: ({0 ~> ty2}ty1)
    (* | TmFix' : forall {Gamma : ctx} {ty : type} {t : term}, *)
    (*     ok_term Gamma t (TyArr ty ty) -> *)
    (*     ok_term Gamma (TmFix t) ty *)
    (* | TmProd' : forall {Gamma : ctx} {ty1 ty2 : type} {t1 t2 : term}, *)
    (*     ok_term Gamma t1 ty1 -> *)
    (*     ok_term Gamma t2 ty2 -> *)
    (*     ok_term Gamma (TmProd t1 t2) (TyProd ty1 ty2) *)
    (* | TmProj1' : forall {Gamma : ctx} {ty1 ty2 : type} {t : term}, *)
    (*     ok_term Gamma t (TyProd ty1 ty2) -> *)
    (*     ok_term Gamma (TmProj F1 t) ty1 *)
    (* | TmProj2' : forall {Gamma : ctx} {ty1 ty2 : type} {t : term}, *)
    (*     ok_term Gamma t (TyProd ty1 ty2) -> *)
    (*     ok_term Gamma (TmProj F2 t) ty2 *)
    (* | TmCon' : forall {Gamma : ctx} {K : con} {d : data} *)
    (*                   {ty1 ty2 : type} {T : tname} {t : term}, *)
    (*     con_in K d ty1 T Gamma.(cons) -> *)
    (*     ok_type Gamma ty2 (KiData d) -> *)
    (*     ok_type Gamma ty2 (KiData (T \:= \{K})) -> *)
    (*     ok_term Gamma t (ty_subst ty1 ty2) -> *)
    (*     ok_term Gamma (TmCon K ty2 t) (TyCon ty2 T) *)
    (* | TmMatch' : forall {Gamma : ctx} {vs : var_ctx} {t t1 t2 : term} *)
    (*                     {ty1 ty2 : type} {p : pat}, *)
    (*     ok_term Gamma t ty1 -> *)
    (*     ok_pat  Gamma p ty1 vs -> *)
    (*     ok_term (Gamma <| vars ::= fun vs' => vs ++ vs' |> <| matches ::= fun ms => Match t p :: ms |> *)
    (*             t1 ty2 -> *)
    (*     ok_term (Gamma <| matches ::= fun ms => NoMatch t p :: ms |>) *)
    (*             t2 ty2 -> *)
    (*     ok_term Gamma (TmMatch t p t1 t2) ty2 *)
    (* | TmNever' : forall {Gamma : ctx} {ty : type}, *)
    (*     matches_contradictory Gamma.(matches) -> *)
    (*     ok_term Gamma TmNever ty *)
    (* | TmType' : forall {Gamma : ctx} {t : term} {ty : type}, *)
    (*     ok_type Gamma ty KiType -> *)
    (*     ok_term (Gamma <| tnames ::= S |>) t ty *)
    (* | TmConDef' : forall {Gamma : ctx} {d : data} *)
    (*                      {ty1 ty2 : type} {T : tname} *)
    (*                      {t : term}, *)
    (*     ok_data Gamma d -> *)
    (*     ok_type (Gamma <| tvars ::= fun tv => KiData d :: tv |>) *)
    (*             ty1 KiType -> *)
    (*     ok_term (Gamma <| cons ::= fun Ks => (d, ty1, T) :: Ks |>) *)
    (*             t ty2 -> *)
    (*     ok_type Gamma ty2 KiType -> *)
    (*     ok_term Gamma (TmConDef d ty1 T t) ty2 *)
    (* | TmSem' : forall {Gamma : ctx} {ty1 ty2 : type} *)
    (*                   {cases : list (pat * term)}, *)
    (*     ok_type Gamma ty1 KiType -> *)
    (*     Forall (fun (c : pat * term) => *)
    (*               exists (vs : var_ctx), *)
    (*                 ok_pat Gamma (fst c) ty1 vs /\ *)
    (*                   ok_term (Gamma <| vars ::= fun vs' => vs ++ vs' |>) *)
    (*                           (snd c) ty2) *)
    (*            cases -> *)
    (*     pats_compatible (LibList.map fst cases) ty1 -> *)
    (*     ok_term *)
    (*       Gamma *)
    (*       (TmSem ty1 cases) *)
    (*       (TySem ty1 ty2 (LibList.map fst cases)) *)
    (* | TmComp' : forall {Gamma : ctx} {ty1 ty2 : type} *)
    (*                    {t1 t2 : term} {ps1 ps2 : list pat}, *)
    (*     ok_term Gamma t1 (TySem ty1 ty2 ps1) -> *)
    (*     ok_term Gamma t2 (TySem ty1 ty2 ps2) -> *)
    (*     pats_compatible (ps1 ++ ps2) ty1 -> *)
    (*     ok_term Gamma (TmComp t1 t2) (TySem ty1 ty2 (ps1 ++ ps2)) *)
    (* | TmSemApp' : forall {Gamma : ctx} {ty1 ty2 : type} *)
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

    Lemma ok_term_weakening :
      forall x b G1 G2 T1 t1,
        x = length G1 ->
        G1 ++ G2 |= t1 ~: T1 ->
        G1 & b ++ map (bshift x) G2 |= shift x t1 ~: tshift x T1.
    Proof.
      introv hasType.
      induction hasType ; simple_math.
      - constructor*. admit.
      - apply (TLam (S x)). rew_list*. admit. admit. apply* ok_term_subst_comm.
      - apply (TTyLam (S X)). rew_list*. admit. admit. admit. apply* ok_term_tsubst_comm.
      - constructors*. admit.
    Admitted.

    Lemma ok_term_subst :
      forall G2 G1 x T1 T2 t1 t2,
        x = length G1 ->
        (G1 & BindVar T2 ++ G2) |= t1 ~: T1 ->
        (G1 & Skip ++ G2) |= t2 ~: T2 ->
        (G1 & Skip ++ G2) |= [x => t2]t1 ~: T1.
    Proof.
      introv Heq hasType1 hasType2.
      remember (G1 & BindVar T2 ++ G2) as G. gen G2.
      induction hasType1; intros; simpls; substs...
      { Case "TmFVar". simple_math. admit. admit. }
      { Case "TmLam". apply* (TLam (length (G1 & Skip ++ G2))). admit.
        rewrite subst_open_comm.
        replaces (length (G1 & Skip ++ G2)) with (length (G1 & BindVar T2 ++ G2)).
        rew_list. simple_math. rew_list in *.
        applys_eq (>> IHhasType1 (G2 & BindVar ty1)).
        rew_list*. rew_list*. admit. rew_list*. simple_math. admit.
        rewrite H.
        (* rewrite subst_open_comm... apply_ih_bind* H1. } *)
    (*   { Case "TmTyLam". apply_fresh* TTyLam as X. apply* ok_kind_strengthening. *)
    (*     rewrite* topen_t_subst_comm. apply_ih_bind* H1. } *)
    (*   { Case "TmTyApp". constructors*. apply* ok_type_strengthening. } *)
    (* Qed. *)

    (* Lemma ok_type_lct : *)
    (*   forall Gamma T k, *)
    (*     Gamma |= T ~:: k -> *)
    (*     lct T. *)
    (* Proof. introv Hk ; induction* Hk. Qed. *)
    (* #[export] *)
    (*  Hint Resolve ok_type_lct : mcore. *)

    (* (* Lemma ok_ctx_concat_inv : forall G2 G1, ok_ctx (G1 ++ G2) -> ok_ctx G1. *) *)
    (* (* Proof. *) *)
    (* (*   induction G2 ; intros. *) *)
    (* (*   - rew_list in H. apply H. *) *)
    (* (*   - specializes IHG2 (G1 & a). rew_list in *. *) *)
    (* (*     apply IHG2 in H. inverts* H. *) *)
    (* (*     + false. apply* nil_eq_last_inv. *) *)
    (* (*     + lets . *) *)
    (* (*       rew_list in H1. *) *)
    (* (*     inverts H1. *) *)
    (* (*   introv Hok. *) *)

    (* Lemma ok_kind_weakening : *)
    (*   forall G2 G1 b k, *)
    (*     ok_kind (G1 ++ G2) k -> *)
    (*     ok_kind (G1 & b ++ G2) k. *)
    (* Proof. introv Hk. induction* Hk. Qed. *)

    (* Lemma ok_type_tname_weakening : *)
    (*   forall G2 G1 T k, *)
    (*     (G1 ++ G2) |= T ~:: k -> *)
    (*     (G1 & BindTName ++ G2) |= T ~:: k. *)
    (* Proof. *)
    (*   introv Hk. *)
    (*   remember (G1 ++ G2) as Gamma. gen G2. *)
    (*   induction* Hk; intros; substs. *)
    (*   { Case "TyFVar". constructors*. constructors. apply* binds_weaken. } *)
    (*   { Case "TyAll". apply_fresh* KAll. apply* ok_kind_weakening. *)
    (*     apply_ih_bind* H1. *)
    (*     constructor*. apply* ok_kind_weakening. } *)
    (* Qed. *)

    (* Lemma ok_ctx_ok_type : *)
    (*   forall Gamma x T, *)
    (*     ok_ctx Gamma -> *)
    (*     var_in x T Gamma -> *)
    (*     Gamma |= T ~:: KiType. *)
    (* Proof. *)
    (*   introv Hctx Hbind. *)
    (*   induction* Hctx ; unfolds var_in ; rew_ctx in *. (* ; try (binds_cases Hbind ; apply_empty* ok_type_weakening). *) *)
    (*   { Case "CtxEmpty". inverts Hbind. } *)
    (*   { Case "CtxTName". apply* ok_type_weakening. *)
    (*     lets Hwot : (Nth_last_inv x _ Hbind). *)
    (*     inverts* EQ. } *)
    (*   { Case "CtxVar". inverts* EQ. } *)
    (* Qed. *)


    (* Lemma ok_term_lct : *)
    (*   forall Gamma t T, *)
    (*     Gamma |= t ~: T -> *)
    (*     lct T. *)
    (* Proof with eauto using ok_type_lct. *)
    (*   introv hasType. *)
    (*   induction* hasType ; simple_math... *)
    (*   { Case "TmLam". constructors... *)
    (*     pick_fresh_gen L y... } *)
    (*   { Case "TmApp". inverts* IHhasType1. } *)
    (*   { Case "TmTyLam". inverts* IHhasType. *)
    (*     assert(Hlct: lct ty2)... *)
    (*     pick_fresh X. rewrite *(@tsubst_intro X). *)
    (*     apply* tsubst_lct. } *)
    (* Qed. *)
    (* #[export] *)
    (*  Hint Resolve ok_term_lct : mcore. *)

    (* Lemma ok_term_lc : *)
    (*   forall Gamma t T, *)
    (*     Gamma |= t ~: T -> *)
    (*     lc t. *)
    (* Proof with eauto using ok_term_lct, ok_type_lct with mcore. *)
    (*   introv Htype. *)
    (*   induction* Htype; intros. *)
    (* Qed. *)
    (* #[export] *)
    (*  Hint Resolve ok_term_lc : mcore. *)

    (* Lemma ok_ctx_push : *)
    (*   forall G1 x b, *)
    (*     ok_ctx (G1 & x ~ b) -> *)
    (*     ok_ctx G1. *)
    (* Proof. *)
    (*   introv Hwf. *)
    (*   inverts Hwf ; try (apply eq_push_inv in H; inverts H as []; substs*. *)
    (*   false. apply *empty_push_inv. *)
    (* Qed. *)

    (* Lemma ok_type_ok_ctx : *)
    (*   forall Gamma T k, *)
    (*     Gamma |= T ~:: k -> *)
    (*     ok_ctx Gamma. *)
    (* Proof. *)
    (*   introv hasType. *)
    (*   induction* hasType; pick_fresh_gen L x; *)
    (*     eauto using ok_ctx_push. *)
    (* Qed. *)
    (* #[export] *)
    (*  Hint Resolve ok_type_ok_ctx : mcore. *)

    (* Lemma ok_term_ok_ctx : *)
    (*   forall Gamma t T, *)
    (*     Gamma |= t ~: T -> *)
    (*     ok_ctx Gamma. *)
    (* Proof. *)
    (*   introv hasType. *)
    (*   induction* hasType; pick_fresh_gen L x; *)
    (*     eauto using ok_ctx_push. *)
    (* Qed. *)
    (* #[export] *)
    (*  Hint Resolve ok_term_ok_ctx : mcore. *)

    (* Lemma ok_term_weakening : *)
    (*   forall G3 G2 G1 t T, *)
    (*     G1 & G3 |= t ~: T -> *)
    (*     ok_ctx (G1 & G2 & G3) -> *)
    (*     G1 & G2 & G3 |= t ~: T. *)
    (* Proof. *)
    (*   introv hasType Hctx. remember (G1 & G3) as H. gen G3. *)
    (*   induction hasType; intros; substs*. *)
    (*   { Case "TmFVar". constructors*. apply* binds_weaken. } *)
    (*   { Case "TmLam". apply_fresh* TLam as y. *)
    (*     - apply* ok_type_weakening. *)
    (*     - apply_ih_bind* H1. *)
    (*       constructors*. *)
    (*       apply* ok_type_weakening. } *)
    (*   { Case "TmTyLam". apply_fresh* TTyLam as X. *)
    (*     - apply* ok_kind_weakening. *)
    (*     - apply_ih_bind* H1. constructors*. apply* ok_kind_weakening. } *)
    (*   { Case "TmTyApp". constructors*. apply* ok_type_weakening. } *)
    (* Qed. *)

    (* Lemma ok_data_strengthening : *)
    (*   forall G1 G2 x T d, *)
    (*     ok_data (G1 & x ~ BindVar T & G2) d -> *)
    (*     ok_data (G1 & G2) d. *)
    (* Proof. *)
    (*   introv Hd. unfolds ok_data. *)
    (*   splits*. introv Hbind. *)
    (*   lets [Hbind' Hk]: (proj2 Hd) Hbind. *)
    (*   splits. *)
    (*   - binds_cases Hbind' ; auto. *)
    (*   - introv Hkin. lets [ ? (? & Hbindk) ] : Hk Hkin. *)
    (*     binds_cases Hbindk ; eauto. *)
    (* Qed. *)

    (* Lemma ok_kind_strengthening : *)
    (*   forall G1 G2 x T k, *)
    (*     ok_kind (G1 & x ~ BindVar T & G2) k -> *)
    (*     ok_kind (G1 & G2) k. *)
    (* Proof. introv Hk. induction* Hk. Qed. *)

    (* Lemma ok_type_strengthening : *)
    (*   forall G1 G2 x T1 T2 k, *)
    (*     G1 & x ~ BindVar T2 & G2 |= T1 ~:: k -> *)
    (*     ok_ctx (G1 & G2) -> *)
    (*     G1 & G2 |= T1 ~:: k. *)
    (* Proof. *)
    (*   introv Htk. remember (G1 & x ~ BindVar T2 & G2) as G. gen G2. *)
    (*   induction Htk; intros; substs*. *)
    (*   { Case "TyFVar". constructors*. *)
    (*     binds_cases H0 ; auto. } *)
    (*   { Case "TyAll". apply_fresh* KAll as X. *)
    (*     apply* ok_kind_strengthening. *)
    (*     apply_ih_bind* H1. constructor*. apply* ok_kind_strengthening. } *)
    (* Qed. *)

    (* Lemma ok_ctx_con_inv : *)
    (*   forall Gamma K d ty T, *)
    (*     ok_ctx (Gamma & K ~ BindCon d ty T) -> *)
    (*     ok_data Gamma d /\ Gamma |= ty ~:: KiType /\ binds T BindTName Gamma. *)
    (* Proof. *)
    (*   introv Hctx. *)
    (*   inverts Hctx ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; splits* ; fequals). *)
    (*   false. apply* empty_push_inv. *)
    (* Qed. *)

    (* Lemma ok_ctx_tvar_inv : *)
    (*   forall Gamma X k, *)
    (*     ok_ctx (Gamma & X ~ BindTVar k) -> *)
    (*     ok_kind Gamma k. *)
    (* Proof. *)
    (*   introv Hctx. *)
    (*   inverts Hctx ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; fequals). *)
    (*   false. apply* empty_push_inv. *)
    (* Qed. *)

    (* Lemma ok_ctx_var_inv : *)
    (*   forall Gamma x T, *)
    (*     ok_ctx (Gamma & x ~ BindVar T) -> *)
    (*     Gamma |= T ~:: KiType. *)
    (* Proof. *)
    (*   introv Hctx. *)
    (*   inverts Hctx ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; fequals). *)
    (*   false. apply* empty_push_inv. *)
    (* Qed. *)

    (* Lemma ok_ctx_strengthening : *)
    (*   forall G1 x T G3, *)
    (*     ok_ctx (G1 & x ~ BindVar T & G3) -> *)
    (*     ok_ctx (G1 & G3). *)
    (* Proof. *)
    (*   introv Hctx. induction G3 using ctx_ind. *)
    (*   { Case "Empty". rewrite concat_empty_r in *. apply* ok_ctx_push. } *)
    (*   { Case "Push". rewrite concat_assoc in *. *)
    (*     specializes IHG3 (ok_ctx_push _ _ _ Hctx). *)
    (*     lets [? Hdisj] : ok_push_inv (ok_ctx_ok _ Hctx). *)
    (*     destruct v. *)
    (*     { SCase "BindTName". constructor~. } *)
    (*     { SCase "BindCon". forwards [ Hd (Htk & HT)]: ok_ctx_con_inv Hctx. *)
    (*       constructor~. *)
    (*       - applys ok_data_strengthening Hd. *)
    (*       - applys* ok_type_strengthening Htk. *)
    (*       - binds_cases HT ; auto. } *)
    (*     { SCase "BindTVar". forwards Hk: ok_ctx_tvar_inv Hctx. *)
    (*       constructor~. applys ok_kind_strengthening Hk. } *)
    (*     { SCase "BindVar". forwards Htk: ok_ctx_var_inv Hctx. *)
    (*       constructor~. applys* ok_type_strengthening Htk. } *)
    (*     { SCase "BindMatch". constructor~. } } *)
    (* Qed. *)

    (* Lemma ok_term_subst : *)
    (*   forall G2 G1 x T1 T2 t1 t2, *)
    (*     G1 & x ~ BindVar T2 & G2 |= t1 ~: T1 -> *)
    (*     G1 |= t2 ~: T2 -> *)
    (*     G1 & G2 |= [x => t2]t1 ~: T1. *)
    (* Proof with eauto using ok_term_lc, ok_ctx_strengthening, ok_type_strengthening with mcore. *)
    (*   introv hasType1 hasType2. *)
    (*   remember (G1 & x ~ BindVar T2 & G2) as G. gen G2. *)
    (*   induction hasType1; intros; simpls; substs... *)
    (*   { Case "TmFVar". solve_var. *)
    (*     - binds_get H0... apply_empty ok_term_weakening... *)
    (*     - binds_cases H0... } *)
    (*   { Case "TmLam". apply_fresh* TLam as y... *)
    (*     rewrite subst_open_comm... apply_ih_bind* H1. } *)
    (*   { Case "TmTyLam". apply_fresh* TTyLam as X. apply* ok_kind_strengthening. *)
    (*     rewrite* topen_t_subst_comm. apply_ih_bind* H1. } *)
    (*   { Case "TmTyApp". constructors*. apply* ok_type_strengthening. } *)
    (* Qed. *)

    (* Lemma ok_data_tvar_strengthening : *)
    (*   forall G1 G2 x k d, *)
    (*     ok_data (G1 & x ~ BindTVar k & G2) d -> *)
    (*     ok_data (G1 & G2) d. *)
    (* Proof. *)
    (*   introv Hd. unfolds ok_data. *)
    (*   splits*. introv Hbind. *)
    (*   lets [Hbind' Hk]: (proj2 Hd) Hbind. *)
    (*   splits. *)
    (*   - binds_cases Hbind' ; auto. *)
    (*   - introv Hkin. lets [ ? (? & Hbindk) ] : Hk Hkin. *)
    (*     binds_cases Hbindk ; eauto. *)
    (* Qed. *)

    (* Lemma ok_data_bsubst : *)
    (*   forall G1 G2 X T d, *)
    (*     ok_data (G1 & G2) d -> *)
    (*     ok_data (G1 & map (bsubst X T) G2) d. *)
    (* Proof. *)
    (*   introv Hd. unfolds ok_data. *)
    (*   splits*. introv Hbind. *)
    (*   lets [Hbind' Hk]: (proj2 Hd) Hbind. *)
    (*   splits. *)
    (*   - binds_cases Hbind' ; auto. *)
    (*     replaces BindTName with (bsubst X T BindTName) ; auto. *)
    (*   - introv Hkin. lets [ d' (ty & Hbindk) ] : Hk Hkin. *)
    (*     binds_cases Hbindk ; eauto. *)
    (*     exists d' ({X => T} ty). *)
    (*     replaces (BindCon d' ({X => T} ty) T0) with (bsubst X T (BindCon d' ty T0)) ; auto. *)
    (* Qed. *)

    (* Lemma ok_kind_tvar_strengthening : *)
    (*   forall G1 G2 x k' k, *)
    (*     ok_kind (G1 & x ~ BindTVar k' & G2) k -> *)
    (*     ok_kind (G1 & G2) k. *)
    (* Proof. introv Hk. induction* Hk. Qed. *)

    (* Lemma ok_kind_bsubst : *)
    (*   forall G1 G2 X T k, *)
    (*     ok_kind (G1 & G2) k -> *)
    (*     ok_kind (G1 & map (bsubst X T) G2) k. *)
    (* Proof. introv Hk. induction* Hk. Qed. *)

    (* Lemma ok_type_tsubst : *)
    (*   forall G1 G2 X T1 T2 k k', *)
    (*     G1 & X ~ BindTVar k' & G2 |= T1 ~:: k -> *)
    (*     G1 |= T2 ~:: k' -> *)
    (*     ok_ctx (G1 & map (bsubst X T2) G2) -> *)
    (*     G1 & map (bsubst X T2) G2 |= {X => T2} T1 ~:: k. *)
    (* Proof with eauto with mcore. *)
    (*   introv Hkt1 Hkt2 Hctx. *)
    (*   remember (G1 & X ~ BindTVar k' & G2) as G. gen G2. *)
    (*   induction Hkt1; intros; substs; simpls*. *)
    (*   { Case "TyFVar". solve_var. *)
    (*     + binds_get H0. lets* [Hok ?] : ok_concat_inv (ok_ctx_ok _ Hctx). *)
    (*       apply_empty* ok_type_weakening. *)
    (*     + binds_cases H0... *)
    (*       constructors*. apply binds_concat_right. *)
    (*       replaces (BindTVar k) with (bsubst X T2 (BindTVar k))... } *)
    (*   { Case "TyAll". assert (Hk : ok_kind (G1 & map (bsubst X T2) G2) k). *)
    (*     apply* ok_kind_bsubst. apply* ok_kind_tvar_strengthening. *)
    (*     apply_fresh* KAll. *)
    (*     assert (lct T2) by apply* ok_type_lct. *)
    (*     rewrite~ tsubst_topen_comm. *)
    (*     replaces (G1 & map (bsubst X T2) G2 & y ~ BindTVar k) *)
    (*       with (G1 & map (bsubst X T2) (G2 & y ~ BindTVar k))... *)
    (*     + autorewrite with rew_ctx_map rew_ctx_concat ; auto. *)
    (*     + apply~ H1. *)
    (*       * autorewrite with rew_ctx_concat ; auto. *)
    (*       * autorewrite with rew_ctx_map rew_ctx_concat... } *)
    (* Qed. *)

    (* Lemma bsubst_ok_ctx : *)
    (*   forall G1 G2 X T2 k, *)
    (*     G1 |= T2 ~:: k -> *)
    (*     ok_ctx (G1 & X ~ BindTVar k & G2) -> *)
    (*     ok_ctx (G1 & map (bsubst X T2) G2). *)
    (* Proof. *)
    (*   introv Htk Hctx. *)
    (*   induction G2 using ctx_ind. *)
    (*   { Case "Empty". autorewrite with rew_ctx_map rew_ctx_concat in *. *)
    (*     apply* ok_ctx_push. } *)
    (*   { Case "Push". autorewrite with rew_ctx_map rew_ctx_concat in *. *)
    (*     specializes IHG2 (ok_ctx_push _ _ _ Hctx). *)
    (*     lets [? Hdisj] : ok_push_inv (ok_ctx_ok _ Hctx). *)
    (*     destruct v. *)
    (*     { SCase "BindTName". constructor~. } *)
    (*     { SCase "BindCon". forwards (Hd & Htk' & HT): ok_ctx_con_inv Hctx. *)
    (*       constructor~. *)
    (*       - applys ok_data_bsubst. apply* ok_data_tvar_strengthening. *)
    (*       - applys* ok_type_tsubst Htk. *)
    (*       - binds_cases HT ; auto. *)
    (*         replaces BindTName with (bsubst X T2 BindTName) ; auto. } *)
    (*     { SCase "BindTVar". forwards Hk: ok_ctx_tvar_inv Hctx. *)
    (*       constructor~. applys ok_kind_bsubst. apply* ok_kind_tvar_strengthening. } *)
    (*     { SCase "BindVar". forwards Htk': ok_ctx_var_inv Hctx. *)
    (*       constructor~. applys* ok_type_tsubst Htk'. } *)
    (*     { SCase "BindMatch". constructor~. } } *)
    (* Qed. *)

    (* Lemma ok_ctx_concat : *)
    (*   forall G1 G2, *)
    (*     ok_ctx (G1 & G2) -> *)
    (*     ok_ctx G1. *)
    (* Proof with eauto. *)
    (*   introv Hctx. *)
    (*   induction G2 using ctx_ind. *)
    (*   { Case "Empty". rew_ctx_concat in *... } *)
    (*   { Case "Push". apply IHG2. rew_ctx_concat in *. *)
    (*     apply* ok_ctx_push. } *)
    (* Qed. *)

    (* Lemma ok_type_notin : *)
    (*   forall Gamma T k X, *)
    (*     Gamma |= T ~:: k -> *)
    (*     X # Gamma -> *)
    (*     X \notin ftv T. *)
    (* Proof. *)
    (*   introv Htk Hfresh. *)
    (*   induction Htk; simpls*. *)
    (*   { Case "TyFVar". intros contra. *)
    (*     rewrite in_singleton in contra. substs. *)
    (*     apply get_none in Hfresh. *)
    (*     apply binds_get in H0. *)
    (*     fequals. } *)
    (*   { Case "TyAll". pick_fresh Y. *)
    (*     forwards~ Hnin: H0 Y. *)
    (*     applys~ topen_notin Y. } *)
    (* Qed. *)

    (* Lemma ctx_bsubst_fresh : *)
    (*   forall Gamma X T2, *)
    (*     ok_ctx Gamma -> *)
    (*     X # Gamma -> *)
    (*     Gamma = map (bsubst X T2) Gamma. *)
    (* Proof with eauto using ok_ctx_push. *)
    (*   introv Hctx Hfresh. *)
    (*   induction Gamma using ctx_ind. *)
    (*   { Case "Empty". rewrite~ map_empty. } *)
    (*   { Case "Push". autorewrite with rew_ctx_map. *)
    (*     rewrite <- IHGamma... *)
    (*     destruct~ v ; repeat fequals ; unfold bsubst ; rewrite* tsubst_fresh. *)
    (*     { SCase "BindCon". *)
    (*       apply ok_ctx_con_inv in Hctx as (? & Hkt & ?). *)
    (*       apply* ok_type_notin. } *)
    (*     { SCase "BindVar". *)
    (*       apply ok_ctx_var_inv in Hctx. *)
    (*       apply* ok_type_notin. } } *)
    (* Qed. *)

    (* Lemma ok_term_tsubst : *)
    (*   forall G2 G1 t k T1 T2 X, *)
    (*     G1 & X ~ BindTVar k & G2 |= t ~: T1 -> *)
    (*     G1 |= T2 ~:: k -> *)
    (*     G1 & map (bsubst X T2) G2 |= [{X => T2}]t ~: ({X => T2}T1). *)
    (* Proof with eauto using ok_ctx_strengthening, bsubst_ok_ctx with mcore. *)
    (*   introv hasType Hctx. *)
    (*   remember (G1 & X ~ BindTVar k & G2) as G. gen G2. *)
    (*   induction hasType; intros; simpls; substs... *)
    (*   { Case "TmFVar". *)
    (*     binds_cases H0 ; constructors ; *)
    (*       replaces (BindVar ({X => T2} ty)) with (bsubst X T2 (BindVar ty))... *)
    (*     apply ok_ctx_concat in H. *)
    (*     assert (X # G1) by apply* ok_push_inv. *)
    (*     rewrite* (@ctx_bsubst_fresh G1 X T2). } *)
    (*   { Case "TmLam". apply_fresh* TLam as x. *)
    (*     + apply* ok_type_tsubst. apply* bsubst_ok_ctx. *)
    (*     + rewrite tsubst_t_open_comm. *)
    (*       replaces (G1 & map (bsubst X T2) G2 & x ~ BindVar ({X => T2}ty1)) *)
    (*         with (G1 & map (bsubst X T2) (G2 & x ~ BindVar ty1)). *)
    (*       autorewrite with rew_ctx_map rew_ctx_concat ; auto. *)
    (*       apply~ H1. rewrite~ concat_assoc. } *)
    (*   { Case "TmTyLam". apply_fresh* TTyLam. *)
    (*     + apply ok_kind_bsubst. apply* ok_kind_tvar_strengthening. *)
    (*     + replaces (G1 & map (bsubst X T2) G2 & y ~ BindTVar k0) *)
    (*         with (G1 & map (bsubst X T2) (G2 & y ~ BindTVar k0)). *)
    (*       autorewrite with rew_env_map rew_env_concat ; auto. *)
    (*       rewrite~ tsubst_topen_comm... *)
    (*       rewrite topen_t_tsubst_comm... *)
    (*       apply~ H1. rewrite~ concat_assoc. } *)
    (*   { Case "TmTyApp". *)
    (*     rewrite tsubst_topen_distr... constructors*. *)
    (*     apply* ok_type_tsubst. } *)
    (* Qed. *)

  End Typing.
End Typing.
