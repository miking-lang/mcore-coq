From TLC Require Import LibString LibLN.
From MCore Require Import Syntax Typing SmallStep Tactics.

Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Module Soundness (PC : PATCHECK) (M : MATCH).
    Module Typing := Typing PC.
    Module SmallStep := SmallStep M.
    Import Typing SmallStep.

    Lemma tname_value_weakening :
      forall G2 G1 ty t T,
        T \notin tfv ty ->
        is_value t ->
        G1 & T ~ BindTName & G2 |= t ~: ty ->
        G1 & G2 |= t ~: ty.
    Admitted.

    Lemma con_value_weakening :
      forall G2 G1 ty t K d ty' T,
        K \notin tfv ty ->
        is_value t ->
        G1 & K ~ BindCon d ty' T & G2 |= t ~: ty ->
        G1 & G2 |= t ~: ty.
    Admitted.

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
        + forwards* Hv : Topen_value Hval.
        + forwards* (t'0 & Hstep') : Topen_step Hstep. }
      { Case "TmConDef". right. pick_fresh K.
        forwards* [Hval | (t' & Hstep)]: H4 K.
        + introv Hb. binds_cases Hb. apply* Hnv.
        + forwards* Hv : Kopen_value Hval.
        + forwards* (t'0 & Hstep') : Kopen_step Hstep. }
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
        pick_fresh x. rewrite* (@subst_intro x).
        apply_empty* ok_term_subst. }
      { Case "TmTyApp". inverts hasType.
        pick_fresh X.
        rewrite* (@tsubst_intro X).
        rewrite* (@tsubst_t_intro X).
        apply_empty~ ok_term_tsubst. }
      { Case "TmType". pick_fresh T.
        assert (Htype : Gamma |= Topen_t 0 (FTName T) t' ~: ty).
        { apply_empty* tname_value_weakening. auto. apply~ value_Topen. }
        forwards~ Hnin : ok_term_notin T Htype.
        forwards Heq : notin_Topen Hnin. rewrite~ Heq in Htype. }
      { Case "TmTypeCong". apply_fresh TType as T ; auto.
        forwards* Hstep': step_Topen t t2. }
      { Case "TmConDef". pick_fresh K.
        assert (Htype : Gamma |= Kopen_t 0 (FCon K) t' ~: ty2).
        { apply_empty* con_value_weakening. auto. apply~ value_Kopen. }
        forwards~ Hnin : ok_term_notin K Htype.
        forwards Heq : notin_Kopen Hnin. rewrite~ Heq in Htype. }
      { Case "TmConDefCong". apply_fresh TConDef as K; auto.
        forwards* Hstep': step_Kopen t t2. }
    Qed.

  End Soundness.
End Soundness.
