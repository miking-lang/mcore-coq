From TLC Require Import LibString LibLN.
From MCore Require Import Syntax Typing SmallStep Tactics.

Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Module Soundness (PC : PATCHECK) (M : MATCH).
    Module Typing := Typing PC.
    Module SmallStep := SmallStep M.
    Import Typing SmallStep.

    Lemma ok_term_Topen_push :
      forall L Gamma t t' ty,
        (forall T, T \notin L ->
              Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty) ->
        push_value TmType t t' ->
        Gamma |= t' ~: ty.
    Proof with eauto with mcore.
      introv Htype Hpush. gen L ty.
      remember TmType as f eqn:Hf.
      induction Hpush ; introv Htype ; substs ;
        pick_fresh T ; forwards~ Htype0: Htype T ; inverts Htype0 ; simpls.
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
        assert (ok_kind Gamma k)
          by (apply_empty~ (ok_kind_tname_strengthening T) ; apply* ok_env_push).
        apply_fresh* TTyLam as X.
        forwards~ Htype': H4 X. apply_fresh TType as T'...
        rewrite~ (Tsubst_t_intro T (FTName T')).
        + rewrite~ <- (Tsubst_ty_fresh T (FTName T')).
          * apply_empty ok_term_Tsubst... rewrite* Topen_t_topen_comm.
            apply_empty~ ok_term_comm. constructor~. constructor~. apply* ok_env_push.
          * rewrite~ topen_notin_T. simpls~.
        + rewrite~ topen_t_notin_T. }
      { Case "TmCon". rewrite notin_Topen_ty in *...
        constructors.
        + binds_cases H2...
        + apply_empty (ok_type_tname_strengthening T) ; auto ; apply* ok_env_push.
        + apply_empty (ok_type_tname_strengthening T) ; auto ; apply* ok_env_push.
        + specializes~ IHHpush __. apply_fresh IHHpush as T'.
          rewrite~ (Tsubst_t_intro T (FTName T')). rewrite~ <- (Tsubst_ty_fresh T (FTName T')).
          * apply_empty~ ok_term_Tsubst.
          * rewrite~ topen_notin_T. binds_cases H2.
            forwards (L'&?&?&?&Htk&?): ok_env_binds_con_inv B. apply* ok_env_push.
            pick_fresh X. forwards~ Hnin: ok_type_notin_T T (Htk X).
            rewrite~ topen_notin_T in Hnin. simpls~. }
    Qed.

    Lemma ok_term_Kopen_push :
      forall Gamma K d ty' T t t' ty,
        Gamma & K ~ BindCon d ty' T |= Kopen_t 0 (FCon K) t ~: ty ->
        push_value (TmConDef d ty' T) t t' ->
        Gamma |= t' ~: ty.
    Admitted.

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
        pick_fresh x. rewrite* (@subst_intro x).
        apply_empty* ok_term_subst. }
      { Case "TmTyApp". inverts hasType.
        pick_fresh X.
        rewrite* (@tsubst_intro X).
        rewrite* (@tsubst_t_intro X).
        apply_empty~ ok_term_tsubst. }
      { Case "TmType". applys* ok_term_Topen_push (L \u Tfv_ty ty). }
      { Case "TmTypeCong". apply_fresh TType as T' ; auto. }
      { Case "TmConDef". pick_fresh K'. applys* ok_term_Kopen_push K'. }
      { Case "TmConDefCong". apply_fresh TConDef as K'; auto. }
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
