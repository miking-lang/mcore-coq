From TLC Require Import LibString LibList LibLN.
From MCore Require Import
     Syntax SyntaxProps Typing TypingProps
     SmallStep SmallStepProps Tactics.

Module Soundness (P : PAT).
  Module SP := SmallStepProps P.
  Import SP.

  Module Soundness1 (PC : PATCHECK) (M : MATCH).
    Module SP1 := SmallStepProps1 PC M.
    Import SP1.

    Module Soundness2 (PP : PATPROPS) (PCP : PATCHECKPROPS) (MP : MATCHPROPS).
      Module SP2 := SmallStepProps2 PP PCP MP.
      Import SP2.

      Theorem preservation :
        forall Gamma t t' ty,
          Gamma |= t ~: ty ->
          t --> t' ->
          Gamma |= t' ~: ty.
      Proof.
        introv hasType Hstep.
        gen t'.
        induction hasType; intros; inverts~ Hstep ;
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
        { Case "TmProj1". inverts* hasType. }
        { Case "TmProj2". inverts* hasType. }
        { Case "TmMatchThen". pick_fresh x. rewrite~ (subst_intro x).
          apply_empty~ ok_term_subst. apply* match1_ok_pat. }
        { Case "TmType". pick_fresh T. applys* ok_term_Topen_push T t. }
        { Case "TmTypeCong". apply_fresh TType as T' ; auto. }
        { Case "TmConDef". pick_fresh K. applys* ok_term_Kopen_push K t. }
        { Case "TmConDefCong". apply_fresh TConDef as K' ; auto. }
        { Case "TmSemApp".
          assert (i < length ps0) by apply* matchN_length.
          forwards* (L&ty1'&Hpat&Htype) : ok_term_get_cases_inv i.
          remember (nth i bs) ; pick_fresh x ; substs. rewrite~ (subst_intro x).
          apply_empty~ ok_term_subst. apply* matchN_ok_pat. }
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
        { Case "TmMatch". right.
          forwards* [Hval | (t' & Hstep)]: IHhasType1.
          destruct (match1 t p) eqn:Hmatch ; auto_star. }
        { Case "TmType". right. pick_fresh T.
          forwards* [Hval | (t' & Hstep)]: H0 T.
          + introv Hb. binds_cases Hb. apply* Hnv.
          + forwards* Hval' : Topen_is_value Hval.
          + rewrite <- (Topen_t_Tclose 0 T t') in Hstep.
            * eexists. apply_fresh ETypeCong.
              apply* Topen_step_change. lets~ ?: Tclose_t_notin T 0 t'.
            * lets* ?: preservation Hstep. }
        { Case "TmConDef". right. pick_fresh K.
          forwards* [Hval | (t' & Hstep)]: H3 K.
          + introv Hb. binds_cases Hb. apply* Hnv.
          + forwards* Hval' : Kopen_is_value Hval.
          + rewrite <- (Kopen_t_Kclose 0 K t') in Hstep.
            * eexists. apply_fresh EConDefCong.
              apply* Kopen_step_change. lets~ ?: Kclose_t_notin K 0 t'.
            * lets* ?: preservation Hstep. }
        { Case "TmComp".
          forwards* [Hval1 | (t1' & Hstep1)]: IHhasType1.
          forwards* [Hval2 | (t2' & Hstep2)]: IHhasType2. }
        { Case "TmSemApp". right.
          forwards* [Hval1 | (t1' & Hstep1)]: IHhasType1.
          forwards* [Hval2 | (t2' & Hstep2)]: IHhasType2.
          forwards* (i&v'&Hmatch): exhaustive_has_match hasType2.
          destruct (get_cases t1) eqn:Hget.
          forwards* Heq : ok_term_get_cases_eq ; substs*. }
      Qed.

    End Soundness2.
  End Soundness1.
End Soundness.
