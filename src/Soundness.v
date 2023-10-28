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
      forall Gamma T t t' ty,
        Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty ->
        push_value TmType t t' ->
        Gamma |= t' ~: ty.
    Proof.
      Admitted.
      (* introv Htype Hpush. *)
      (* remember TmType as f eqn:Hf. *)
      (* induction Hpush ; substs. *)
      (* - inverts Htype. *)
      (*   assert (Topen_ty 0 (FTName T) ty0 = ty0) by admit. *)
      (*   rewrite H in *. *)
      (*   apply_fresh TLam as x. admit. *)
      (*   (* apply_empty ok_type_tname_strengthening. *) *)
      (*   simpls. apply_fresh TType as T'. *)

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
      { Case "TmType". pick_fresh T'. applys* ok_term_Topen_push T'. }
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
        + forwards (tclose & Heq): Topen_t_close 0 (FTName T) t'.
          * forwards* ?: preservation Hstep.
          * substs. eexists. apply_fresh ETypeCong.
            apply* Topen_step_change. }
      { Case "TmConDef". right. pick_fresh K.
        forwards* [Hval | (t' & Hstep)]: H4 K.
        + introv Hb. binds_cases Hb. apply* Hnv.
        + forwards Hval' : Kopen_is_value Hval.
          forwards* (v' & Hpush): is_value_push Hval'.
        + forwards (tclose & Heq) : Kopen_t_close 0 (FCon K) t'.
          * forwards* ?: preservation Hstep.
          * substs. eexists. apply_fresh EConDefCong.
            apply* Kopen_step_change. }
    Qed.

  End Soundness.
End Soundness.
