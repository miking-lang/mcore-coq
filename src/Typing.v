From MCore Require Import Syntax Env Tactics.
From TLC Require Import LibString LibNat LibList LibSet.

Open Scope nat_scope.

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

    (*********************************)
    (** TYPING RELATION DEFINITIONS **)
    (*********************************)

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
        tvar_in tv k Gamma ->
        ok_type Gamma (TyFVar tv) k
    | TyArr' : forall {Gamma : env} {ty1 ty2 : type},
        ok_type Gamma ty1 KiType ->
        ok_type Gamma ty2 KiType ->
        ok_type Gamma (TyArr ty1 ty2) KiType
    | TyAll' : forall {Gamma : env} {k : kind} {ty : type},
        ok_type (BindTVar k :: Gamma) (ty_open ty 0 0) KiType ->
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
    | EnvTName : forall Gamma, ok_env Gamma -> ok_env (BindTName :: Gamma)
    | EnvCon   :
      forall Gamma d ty T,
        ok_env Gamma ->
        ok_data Gamma d ->
        ok_type Gamma ty KiType ->
        tname_in T (tnames Gamma) ->
        ok_env (BindCon d ty T :: Gamma)
    | EnvTVar : forall Gamma k,
        ok_env Gamma ->
        ok_kind Gamma k ->
        ok_env (BindTVar k :: Gamma)
    | EnvVar : forall Gamma ty,
        ok_env Gamma ->
        ok_type Gamma ty KiType ->
        ok_env (BindVar ty :: Gamma)
    | EnvMatch : forall Gamma m,
        ok_env Gamma ->
        ok_env (BindMatch m :: Gamma)
    .
    #[export]
     Hint Constructors ok_env : mcore.

    Inductive ok_term : env -> term -> type -> Prop :=
    | TmFVar' : forall {Gamma : env} {x : var} {ty : type},
        ok_env Gamma ->
        var_in x ty Gamma ->
        ok_term Gamma (TmFVar x) ty
    | TmLam' : forall {Gamma : env} {ty1 ty2 : type} {t : term},
        ok_type Gamma ty1 KiType ->
        ok_term (BindVar ty1 :: Gamma) (tm_open t 0 0) ty2 ->
        ok_term Gamma (TmLam ty1 t) (TyArr ty1 ty2)
    | TmApp' : forall {Gamma : env} {ty1 ty2 : type} {t1 t2 : term},
        ok_term Gamma t1 (TyArr ty1 ty2) ->
        ok_term Gamma t2 ty1 ->
        ok_term Gamma (TmApp t1 t2) ty2
    | TmTyLam' : forall {Gamma : env} {k : kind} {ty : type} {t : term},
        ok_kind Gamma k ->
        ok_term (BindTVar k :: freshen_after Gamma)
                (tm_ty_open t 0 0) (ty_open ty 0 0) ->
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


    (**************************)
    (** PROPERTIES OF TYPING **)
    (**************************)

    Lemma ok_type_lct :
      forall Gamma ty k,
        ok_type Gamma ty k ->
        ty_lc ty.
    Proof. introv tykind. induction* tykind. Qed.
    #[export]
     Hint Resolve ok_type_lct : mcore.

    Lemma ok_env_type :
      forall G1 G2 ty,
        ok_env (G1 ++ BindVar ty :: G2) ->
        ok_type G2 ty KiType.
    Proof. introv Henv ; induction* G1 ; inverts* Henv. Qed.

    Lemma ok_env_lct :
      forall Gamma x ty,
        ok_env Gamma ->
        var_in x ty Gamma ->
        ty_lc ty.
    Proof.
      introv Henv Hvar. unfolds vars.
      forwards Hmem : Nth_mem Hvar.
      forwards* [ Hmem' ? ] : mem_filter_inv Hmem.
      forwards [ G1 (G2 & Heq) ] : mem_inv_middle Hmem' ; subst.
      applys ok_type_lct.
      applys* ok_env_type.
    Qed.

    Lemma ok_term_lct :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        ty_lc ty.
    Proof with eauto using ty_lc_fsubst with mcore.
      introv ttype. induction* ttype.
      { Case "TmVar". apply* ok_env_lct. }
      { Case "TmApp". inverts* IHttype1. }
      { Case "TmTyApp".
        rewrite ty_bsubst_close_open with (x := 0).
        inverts IHttype... }
    Qed.
    #[export]
     Hint Resolve ok_term_lct : mcore.

    Lemma ok_term_lc :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        tm_lc t.
    Proof. introv ttype. induction* ttype. Qed.
    #[export]
     Hint Resolve ok_term_lc : mcore.

    Lemma ok_data_weaken_var :
      forall G1 G2 ty' d,
        ok_data (G1 ++ G2) d ->
        ok_data (G1 ++ BindVar ty' :: G2) d.
    Proof. introv Hd. unfolds ok_data. rew_env* in *. Qed.

    Lemma ok_kind_weaken_var :
      forall G1 G2 ty' k,
        ok_kind (G1 ++ G2) k ->
        ok_kind (G1 ++ BindVar ty' :: G2) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_kind_weaken_tvar :
      forall G1 G2 k' k,
        ok_kind (G1 ++ G2) k ->
        ok_kind (G1 ++ BindTVar k' :: G2) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_type_weaken_var :
      forall G1 G2 ty ty' k,
        ok_type (G1 ++ G2) ty k ->
        ok_type (G1 ++ BindVar ty' :: G2) ty k.
    Proof.
      introv Hty.
      remember (G1 ++ G2) as Gamma eqn:HGamma.
      gen G1.
      induction Hty ; intros ; subst*.
      { Case "TyFVar". constructor. unfolds tvar_in. rew_env* in *. }
      { Case "TyAll". constructor. applys IHHty (BindTVar k :: G1). rew_list*. }
    Qed.

    Lemma ok_type_weaken_tvar :
      forall G1 G2 x ty k' k,
        x = length (tvars G1) ->
        ok_type (G1 ++ G2) ty k ->
        ok_type (freshen_before G1 ++ BindTVar k' :: freshen_after G2) (ty_freshen ty x) k.
    Proof.
      introv Heq Hty.
      remember (G1 ++ G2) as Gamma eqn:HGamma.
      gen G1 x.
      induction Hty ; intros ; subst*.
      { Case "TyFVar". unfold ty_freshen. simple_math. admit. admit. }
      Admitted.

    Lemma ok_term_weaken_var :
      forall G1 G2 x t ty ty',
        x = length (vars G1) ->
        ok_term (G1 ++ G2) t ty ->
        ok_env  (G1 ++ BindVar ty' :: G2) ->
        ok_term (G1 ++ BindVar ty' :: G2) (tm_freshen t x) ty.
    Proof with rew_env ; rew_list ; eauto using ok_kind_weaken_var, ok_type_weaken_var with mcore.
    Admitted.
    (*   introv Heq ttype. *)
    (*   remember (G1 ++ G2) as Gamma eqn:HGamma. *)
    (*   gen G1 x. *)
    (*   induction ttype ; intros ; subst ; simpls... *)
    (*   { Case "TmFVar". unfolds var_in. rew_env in *. *)
    (*     forwards [ (Hlt & Hvar) | (Hge & Hvar) ] *)
    (*       : binds_weaken ; simple_math ; constructor ; unfolds var_in... } *)
    (*   { Case "TmLam". constructor... rewrite* tm_open_freshen_comm. *)
    (*     applys IHttype (BindVar ty1 :: G1)... } *)
    (*   { Case "TmTyLam". constructor... rewrite* tm_ty_open_freshen_comm. *)
    (*     apply (IHttype (BindTVar k :: (map_vars (fun ty'0 => ty_freshen ty'0 0) G1)))... } *)
    (* Qed. *)

    (* Lemma ok_env_freshen : *)
    (*   forall G1 G2 k, *)
    (*     ok_env (G1 ++ G2) -> *)
    (*     ok_kind G2 k -> *)
    (*     ok_env (map_vars ty_freshen G1 ++ BindTVar k :: G2). *)
    (* Proof. *)
    (*   introv Henv Hk. *)
    (*   induction G1. *)
    (*   Admitted. *)
    (*   { Case "nil". unfold env_freshen. rew_listx*. } *)
    (*   { Case "cons". unfold env_freshen. rew_listx. } *)
    (* Admitted. *)

    Lemma ok_term_weaken_tvar :
      forall G1 G2 x t ty k,
        x = length (tvars G1) ->
        ok_term (G1 ++ G2) t ty ->
        ok_env  (freshen_before G1 ++ BindTVar k :: G2) ->
        ok_term (freshen_before G1 ++ BindTVar k :: G2) (tm_ty_freshen t x) (ty_freshen ty x).
    Proof with rew_env ; rew_list ; eauto using ok_kind_weaken_tvar, ok_type_weaken_tvar with mcore.
      introv Heq ttype.
      remember (G1 ++ G2) as Gamma eqn:HGamma.
      gen G1 x.
      induction ttype ; intros ; subst ; simpls*.
      Admitted.
      (* { Case "TmFVar". constructor*. unfolds var_in. rew_env in *... } *)
      (* { Case "TmLam". constructor. unfolds var_in. rew_env in *... } *)

    Lemma ok_data_strengthen_var :
      forall G1 G2 ty' d,
        ok_data (G1 ++ BindVar ty' :: G2) d ->
        ok_data (G1 ++ G2) d.
    Proof. introv Hd. unfolds ok_data. rew_env* in *. Qed.

    Lemma ok_kind_strengthen_var :
      forall G1 G2 ty' k,
        ok_kind (G1 ++ BindVar ty' :: G2) k ->
        ok_kind (G1 ++ G2) k.
    Proof. introv Hk. induction* Hk. Qed.

    Lemma ok_type_strengthen_var :
      forall G1 G2 ty' ty k,
        ok_type (G1 ++ BindVar ty' :: G2) ty k ->
        ok_type (G1 ++ G2) ty k.
    Proof.
      introv Hty.
      remember (G1 ++ BindVar ty' :: G2) as Gamma eqn:HGamma.
      gen G1.
      induction Hty ; intros ; subst*.
      { Case "TyFVar". constructor. unfolds tvar_in. rew_env* in *. }
      { Case "TyAll". constructor. applys IHHty (BindTVar k :: G1). rew_list*. }
    Qed.

    Lemma ok_env_strengthen_var :
      forall G1 G2 ty,
        ok_env (G1 ++ BindVar ty :: G2) ->
        ok_env (G1 ++ G2).
    Proof with eauto using ok_data_strengthen_var, ok_kind_strengthen_var, ok_type_strengthen_var.
      introv Henv ; induction* G1 ; rew_list in * ; inverts* Henv ; constructor ; rew_env in *...
    Qed.

    Lemma ok_term_ok_env :
      forall Gamma t ty,
        ok_term Gamma t ty ->
        ok_env Gamma.
    Proof. introv ttype ; induction* ttype ; inverts* IHttype. Admitted.

    Lemma tm_close_preservation :
      forall G1 G2 x t t' ty1 ty2,
        x = length (vars G1) ->
        ok_term (G1 ++ BindVar ty1 :: G2) t ty2 ->
        ok_term (G1 ++ G2) t' ty1 ->
        ok_term (G1 ++ G2) (tm_close t x t') ty2.
    Proof with rew_env ; rew_list
      ; eauto using ok_term_ok_env, ok_kind_strengthen_var, ok_type_strengthen_var, ok_env_strengthen_var
        with mcore.
      introv Heq ttype. unfolds tm_close.
      remember (G1 ++ BindVar ty1 :: G2) as Gamma eqn:HGamma.
      gen ty1 t' G1 x.
      induction ttype ; intros ; subst ; simpls...
      { Case "TmFVar". unfolds var_in. rew_env in *.
        forwards [ (Hlt & Hvar') | [ (Heq1 & Heq2) | (Hgt & Hvar') ] ]
          : binds_app_middle_inv ; subst ; simple_math ; try (constructor ; unfolds var_in)...
        inverts* Heq2. rewrite* tm_defreshen_freshen. }
      { Case "TmLam". constructor... folds (tm_close t (length (vars G1)) t').
        rewrite* tm_open_close_comm. applys IHttype (BindVar ty1 :: G1)...
        applys_eq (ok_term_weaken_var empty_env)... }
      { Case "TmTyLam". constructor... folds (tm_close t (length (vars G1)) t').
        rewrite* tm_ty_open_close_comm. unfolds freshen_after. rew_listx in *.
        apply (IHttype (ty_freshen ty1 0) (tm_ty_freshen t' 0) (BindTVar k :: freshen_after G1)).
        applys_eq (ok_term_weaken_tvar empty_env)... }
    Qed.

    Lemma tm_ty_close_preservation :
      forall Gamma t ty ty' k,
        ok_term (BindTVar k :: Gamma) (tm_ty_open t 0 0) (ty_open ty 0 0) ->
        ok_type Gamma ty' k ->
        ok_term Gamma (tm_ty_bsubst t 0 ty') (ty_bsubst ty 0 ty').
    Proof. Admitted.

  End Typing.
End Typing.
