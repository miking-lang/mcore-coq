From TLC Require Import LibString LibList LibLN.
From MCore Require Import Syntax Typing SmallStep Tactics.
Import LibListNotation.

Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Module Soundness (PC : PATCHECK) (M : MATCH).
    Module Typing := Typing PC.
    Module SmallStep := SmallStep M.
    Import Typing SmallStep.

    Lemma ok_term_Topen_push :
      forall T Gamma t t' ty,
        T \notin dom Gamma \u Tfv_t t \u Tfv_ty ty ->
        Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty ->
        push_value TmType t t' ->
        Gamma |= t' ~: ty.
    Proof with eauto with mcore.
      introv Hfresh Htype Hpush. gen ty.
      remember TmType as f eqn:Hf.
      induction Hpush ; introv Hfresh Htype ; substs ; inverts Htype ; simpls.
      { Case "TmLam". rewrite notin_Topen_ty in *...
        assert (Gamma |= ty ~:: KiType)
          by (apply_empty~ (ok_type_tname_strengthening T) ; apply* ok_env_push).
        apply_fresh* TLam as x.
        forwards~ Htype': H4 x. apply_fresh TType as T'...
        rewrite~ (Tsubst_t_intro T (FTName T')).
        + rewrite~ <- (Tsubst_ty_fresh T (FTName T')). apply_empty ok_term_Tsubst...
          rewrite* Topen_t_open_comm. apply_empty ok_term_comm...
        + rewrite~ open_notin_T. }
      { Case "TmTyLam". rewrite notin_Topen_k in *...
        assert (ok_kind Gamma k) by apply_empty~ (ok_kind_tname_strengthening T).
        apply_fresh* TTyLam as X.
        forwards~ Htype': H4 X. apply_fresh TType as T'...
        rewrite~ (Tsubst_t_intro T (FTName T')).
        + rewrite~ <- (Tsubst_ty_fresh T (FTName T')).
          * apply_empty ok_term_Tsubst... rewrite* Topen_t_topen_comm.
            apply_empty~ ok_term_comm. constructor~. constructor~. apply* ok_env_push.
          * rewrite~ topen_notin_T. simpls~.
        + rewrite~ topen_t_notin_T. }
      { Case "TmProd". constructor*. }
      { Case "TmCon". rewrite notin_Topen_ty in *...
        constructors.
        + binds_cases H2...
        + apply_empty (ok_type_tname_strengthening T) ; auto ; apply* ok_env_push.
        + apply_empty (ok_type_tname_strengthening T) ; auto ; apply* ok_env_push.
        + specializes~ IHHpush __. apply~ IHHpush.
          assert (T \notin Tfv_ty ({0 ~> ty} ty1))...
          rewrite~ topen_notin_T. binds_cases H2.
          forwards (L'&?&?&?&Htk&?): ok_env_binds_con_inv B. apply* ok_env_push.
          pick_fresh X. forwards~ Hnin: ok_type_notin_T T (Htk X).
          rewrite~ topen_notin_T in Hnin. simpls~. }
    Qed.

    Lemma ok_term_Kopen_push :
      forall K Gamma d ty' T t t' ty,
        K \notin dom Gamma \u Kfv_t t \u Kfv_ty ty ->
        Gamma & K ~ BindCon d ty' T |= Kopen_t 0 (FCon K) t ~: ty ->
        push_value (TmConDef d ty' T) t t' ->
        Gamma |= t' ~: ty.
    Proof with eauto with mcore.
      introv Hfresh Htype Hpush. gen ty.
      remember (TmConDef d ty' T) as f eqn:Hf.
      induction Hpush ; introv Hfresh Htype ;
        forwards Henv : ok_term_ok_env Htype ;
        forwards (L0 & T' & Heq & Hd & Htk & HT): ok_env_con_inv Henv ;
        inverts Htype ; substs ; simpls.
      { Case "TmLam". assert (Heq: Kopen_ty 0 (FCon K) ty = ty) by apply~ notin_Kopen_ty.
        rewrite Heq in *.
        assert (Gamma |= ty ~:: KiType)
          by (apply_empty~ (ok_type_con_strengthening K) ; eauto ; apply* ok_env_push).
        assert (Hty' : forall x X,
                   X \notin L0 \u dom Gamma \u \{x} ->
                   x # Gamma ->
                   Gamma & x ~ BindVar ty & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X} ty' ~:: KiType).
        { introv Hnin Hfr. forwards~ Htk' : Htk X. apply~ ok_type_weakening.
          constructor*. constructor~. apply_empty~ ok_data_weakening. constructor*. }
        apply_fresh* TLam as x.
        forwards~ Htype': H4 x. apply_fresh TConDef as K'...
        - apply_empty ok_data_weakening...
        - rewrite~ (Ksubst_t_intro K (FCon K')).
          + rewrite~ <- (Ksubst_ty_fresh K (FCon K')). apply_empty ok_term_Ksubst...
            rewrite* Kopen_t_open_comm. apply_empty~ ok_term_comm.
            apply_fresh EnvCon as X... apply_empty~ ok_data_weakening. constructor...
          + rewrite~ open_notin_K. }
      { Case "TmTyLam". assert (Heq: Kopen_k 0 (FCon K) k = k) by apply~ notin_Kopen_k.
        rewrite Heq in *.
        assert (ok_kind Gamma k) by apply_empty* (ok_kind_con_strengthening K).
        assert (Heq' : forall x, {1 ~> TyFVar x}ty' = ty').
        { intros. pick_fresh y. apply topen_neq with (J := 0) (V := TyFVar y)...
          rewrite~ topen_lct. apply* ok_type_lct. }
        assert (Hty' : forall x X,
                   X \notin L0 \u dom Gamma \u \{x} ->
                   x # Gamma ->
                   Gamma & x ~ BindTVar k & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X} ty' ~:: KiType).
        { introv Hnin Hfr. forwards~ Htk' : Htk X. apply~ ok_type_weakening.
          constructor*. constructor~. apply_empty~ ok_data_weakening. constructor*. }
        apply_fresh* TTyLam as X.
        forwards~ Htype': H4 X. apply_fresh TConDef as K'...
        - apply_empty ok_data_weakening...
        - rewrite~ Heq'.
        - rewrite Heq'. rewrite~ (Ksubst_t_intro K (FCon K')).
          + rewrite~ <- (Ksubst_ty_fresh K (FCon K')).
            * apply_empty ok_term_Ksubst... rewrite* Kopen_t_topen_comm. apply_empty~ ok_term_comm.
              apply_fresh EnvCon as X... apply_empty~ ok_data_weakening. constructor...
            * rewrite~ topen_notin_K. simpls~.
          + rewrite~ topen_t_notin_K. }
      { Case "TmProd". constructor*. }
      { Case "TmCon". assert (Heq: Kopen_ty 0 (FCon K) ty = ty) by apply~ notin_Kopen_ty.
        rewrite Heq in *.
        assert (Htk1 : Gamma |= ty ~:: KiData [ (FTName T0, FCon K1 :: []) ]).
        { apply_empty* (ok_type_con_strengthening K). }
        assert (Hneq : K1 <> K).
        { intro ; subst. forwards~ Hk : ok_type_ok_kind Htk1.
          inverts Hk as Hd'. inverts Hd'. inverts H11.
          assert (K \indom Gamma) by applys get_some_inv H14.
          assert (K # Gamma) by apply* ok_push_inv... }
        replaces K0 with (FCon K1). { destruct K0 ; solve_var. }
        constructors~.
        + binds_cases H2...
        + apply_empty (ok_type_con_strengthening K) ; eauto ; apply* ok_env_push.
        + specializes~ IHHpush __. apply~ IHHpush.
          assert (K \notin Kfv_ty ({0 ~> ty} ty1))...
          rewrite~ topen_notin_K. binds_cases H2.
          forwards (L'&?&?&?&Htk'&?): ok_env_binds_con_inv B. apply* ok_env_push.
          pick_fresh X. forwards~ Hnin': ok_type_notin_K K (Htk' X).
          rewrite~ topen_notin_K in Hnin'. simpls~. }
    Qed.

    Theorem preservation :
      forall Gamma t t' ty,
        Gamma |= t ~: ty ->
        t --> t' ->
        Gamma |= t' ~: ty.
    Proof.
      introv hasType Hstep.
      gen t'.
      induction hasType; intros; inverts Hstep ;
        try (with_hyp (is_context _) as ctx ; with_hyp (_ = _) as eq
             ; inverts ctx ; inverts* eq).
      { Case "TmApp". inverts hasType1.
        pick_fresh x. rewrite~ (subst_intro x).
        apply_empty~ ok_term_subst. }
      { Case "TmTyApp". inverts hasType.
        pick_fresh X.
        rewrite* (tsubst_intro X).
        rewrite* (tsubst_t_intro X).
        apply_empty~ ok_term_tsubst. }
      { Case "TmFix". inverts hasType.
        pick_fresh x. rewrite~ (subst_intro x).
        apply_empty* ok_term_subst. }
      { Case "TmProd". inverts* hasType. }
      { Case "TmProj1". inverts* hasType. }
      { Case "TmType". pick_fresh T. applys* ok_term_Topen_push T t. }
      { Case "TmTypeCong". apply_fresh TType as T' ; auto. }
      { Case "TmConDef". pick_fresh K. applys* ok_term_Kopen_push K t. }
      { Case "TmConDefCong". apply_fresh TConDef as K' ; auto. }
    Qed.

    Definition no_vars (Gamma : env) : Prop :=
      forall x ty, binds x (BindVar ty) Gamma -> False.

    Theorem progress :
      forall Gamma t ty,
        no_vars Gamma ->
        Gamma |= t ~: ty ->
        is_value t \/ exists t', t --> t'.
    Proof.
      introv Hnv hasType.
      induction hasType; substs*.
      { Case "TmFVar". false. apply* Hnv. }
      { Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHhasType1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHhasType2.
        inverts Hval1; inverts* hasType1. }
      { Case "TmTyApp". right.
        forwards* [Hval | (t1 & Hstep)]: IHhasType.
        inverts Hval; inverts* hasType. }
      { Case "TmFix". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHhasType.
        inverts Hval1; inverts* hasType. }
      { Case "TmProd".
        forwards* [Hval1 | (t1' & Hstep1)]: IHhasType1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHhasType2. }
      { Case "TmProj1".
        forwards* [Hval1 | (t1' & Hstep1)]: IHhasType.
        inverts Hval1; inverts* hasType. }
      { Case "TmProj2".
        forwards* [Hval1 | (t1' & Hstep1)]: IHhasType.
        inverts Hval1; inverts* hasType. }
      { Case "TmCon".
        forwards* [Hval | (t' & Hstep)]: IHhasType. }
      { Case "TmType". right. pick_fresh T.
        forwards* [Hval | (t' & Hstep)]: H1 T.
        + introv Hb. binds_cases Hb. apply* Hnv.
        + forwards Hval' : Topen_is_value Hval.
          forwards* (v' & Hpush): is_value_push Hval'.
        + rewrite <- (Topen_t_Tclose 0 T t') in Hstep.
          * eexists. apply_fresh ETypeCong.
            apply* Topen_step_change. lets~ ?: Tclose_t_notin T 0 t'.
          * lets* ?: preservation Hstep. }
      { Case "TmConDef". right. pick_fresh K.
        forwards* [Hval | (t' & Hstep)]: H4 K.
        + introv Hb. binds_cases Hb. apply* Hnv.
        + forwards Hval' : Kopen_is_value Hval.
          forwards* (v' & Hpush): is_value_push Hval'.
        + rewrite <- (Kopen_t_Kclose 0 K t') in Hstep.
          * eexists. apply_fresh EConDefCong.
            apply* Kopen_step_change. lets~ ?: Kclose_t_notin K 0 t'.
          * lets* ?: preservation Hstep. }
    Qed.

  End Soundness.
End Soundness.
