From TLC Require Import LibString LibOption LibList LibLN.
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
      Proof with eauto using ok_type_lct with mcore.
        introv hasType Hstep.
        gen t'.
        induction hasType; intros; inverts Hstep ;
          try (with_hyp (is_context _) as ctx ; with_hyp (_ = _) as eq ;
               inverts ctx ; inverts eq)...
        { Case "TmApp". inverts hasType1.
          pick_fresh x. rewrite~ (subst_intro x).
          apply_empty* ok_term_subst. }
        { Case "TmFixApp". inverts hasType1.
          pick_fresh f. rewrite~ (subst_intro f t).
          rewrite~ <- (subst_fresh f t2 (TmFix ty1 ty2 t)).
          rewrite* <- subst_open_distr. apply_empty* ok_term_subst.
          remember ([0 ~> TmFVar f] t). pick_fresh x ; substs.
          rewrite~ (subst_intro x). apply_empty* ok_term_subst.
          apply_empty* ok_term_weakening. }
        { Case "TmTyApp". inverts hasType.
          pick_fresh X.
          rewrite (tsubst_intro X)...
          rewrite (tsubst_t_intro X)...
          apply_empty* ok_term_tsubst. }
        { Case "TmProj1". inverts* hasType. }
        { Case "TmProj2". inverts* hasType. }
        { Case "TmMatchThen". pick_fresh M. pick_fresh x. rewrite~ (subst_intro x).
          assert (Gamma & M ~ BindMatch t p true |= [x => v'] ([0 ~> TmFVar x] t1) ~: ty2).
          { apply_empty~ ok_term_subst ; try constructors*. applys* match1_value H10. apply* match1_ok_pat.
            apply_empty~ ok_pat_weakening ; try constructors*. apply H. }
          replaces true with (is_some (match1 t p)) in H4. rewrite~ H10.
          apply_empty ok_term_drop_match... }
        { Case "TmMatchElse". pick_fresh M.
          replaces false with (is_some (match1 t p)) in H2. rewrite~ H10.
          apply_empty ok_term_drop_match... applys~ H2 M. }
        { Case "TmMatchCong". forwards* Htk : ok_pat_ok_type.
          apply_fresh TMatch ; intros...
          - applys~ ok_term_step_match t.
            constructor~. constructors... apply_empty~ ok_type_weakening. constructors...
          - apply_empty~ ok_term_step_match. constructors... }
        { Case "TmType". pick_fresh T. applys* ok_term_Topen_push T t. }
        { Case "TmTypeCong". apply_fresh TType as T' ; auto. }
        { Case "TmConDef". pick_fresh K. applys* ok_term_Kopen_push K t. }
        { Case "TmConDefCong". apply_fresh TConDef as K' ; auto. }
        { Case "TmSemApp".
          assert (i < length ps0) by apply* matchN_length.
          forwards* (L&ty1'&Hpat&Htype) : ok_term_get_cases_inv i.
          remember (nth i bs) ; pick_fresh x ; substs. rewrite~ (subst_intro x).
          apply_empty* ok_term_subst. applys* matchN_value H6. apply* matchN_ok_pat. }
      Qed.

      Definition no_vars (Gamma : env) : Prop :=
        forall x ty, binds x (BindVar ty) Gamma -> False.

      Theorem progress :
        forall Gamma t ty,
          no_vars Gamma ->
          ~ contradictory Gamma ->
          Gamma |= t ~: ty ->
          is_value t \/ exists t', t --> t'.
      Proof.
        introv Hnv Hnc hasType.
        induction hasType; substs*.
        { Case "TmFVar". false. apply* Hnv. }
        { Case "TmApp". right.
          forwards* [Hval1 | (t1' & Hstep1)]: IHhasType1.
          forwards* [Hval2 | (t2' & Hstep2)]: IHhasType2.
          inverts Hval1; inverts* hasType1. }
        { Case "TmTyApp". right.
          forwards* [Hval | (t1 & Hstep)]: IHhasType.
          inverts Hval; inverts* hasType. }
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
          forwards* [Hval | (t' & Hstep)]: IHhasType.
          destruct (match1 t p) eqn:Hmatch ; auto_star. }
        { Case "TmType". right. pick_fresh T.
          forwards* [Hval | (t' & Hstep)]: H0 T.
          + introv Hb. binds_cases Hb. apply* Hnv.
          + intro. apply Hnc. apply_empty* (contradictory_tname_strengthening T).
          + forwards* Hval' : Topen_is_value Hval.
          + rewrite <- (Topen_t_Tclose 0 T t') in Hstep.
            * eexists. apply_fresh ETypeCong.
              apply* Topen_step_change. lets~ ?: Tclose_t_notin T 0 t'.
            * lets* ?: preservation Hstep. }
        { Case "TmConDef". right. pick_fresh K.
          forwards* [Hval | (t' & Hstep)]: H3 K.
          + introv Hb. binds_cases Hb. apply* Hnv.
          + intro. apply Hnc. apply_empty* (contradictory_con_strengthening K).
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
