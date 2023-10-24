From TLC Require Import LibString LibList.
From MCore Require Import Syntax Typing SmallStep Tactics.
Import LibListNotation.

Open Scope liblist_scope.

Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Module Soundness (PC : PATCHECK) (M : MATCH).
    Module Typing := Typing PC.
    Module SmallStep := SmallStep M.
    Import Typing SmallStep.

    Theorem progress :
      forall t ty,
        empty |= t ~: ty ->
        is_value t \/ exists t', t --> t'.
    Proof.
      introv hasType.
      remember empty as Gamma.
      induction hasType; substs*.
      { Case "TmFVar". inverts H0. }
      { Case "TmApp". right.
        forwards* [Hval1 | (t1' & Hstep1)]: IHhasType1.
        forwards* [Hval2 | (t2' & Hstep2)]: IHhasType2.
        inverts Hval1; inverts* hasType1. }
      { Case "TmTyApp". right.
        forwards* [Hval | (t1 & Hstep)]: IHhasType.
        inverts Hval; inverts* hasType. }
    Qed.

    Theorem preservation :
      forall G1 t t' ty,
        G1 |= t ~: ty ->
        t --> t' ->
        exists G2, refines G1 G2 /\ G2 |= t' ~: ty.
    Proof.
      introv hasType Hstep.
      gen t'.
      induction hasType; intros.
      - inverts Hstep.
        try (with_hyp (is_context _) as ctx ; with_hyp (_ = _) as eq ; inverts ctx ; inverts* eq).
      - inverts Hstep.
        try (with_hyp (is_context _) as ctx ; with_hyp (_ = _) as eq ; inverts ctx ; inverts* eq).
      - Case "TmApp". inverts* Hstep. inverts hasType1.
        rewrite* (@subst_intro (length Gamma)).
        assert (Gamma & Skip |= [length Gamma => t2] ([0 ~> TmFVar (length Gamma)] t) ~: ty2).
        applys_eq (ok_term_subst empty Gamma) ; rew_list*.
        exists (Gamma & Skip). split. admit. auto. admit.
        with_hyp (is_context _) as ctx. inverts ctx.
      { Case "TmTyApp". inverts hasType.
        pick_fresh X.
        rewrite* (@tsubst_intro X).
        rewrite* (@tsubst_t_intro X).
        apply_empty~ ok_term_tsubst. }
    Qed.

  End Soundness.
End Soundness.
