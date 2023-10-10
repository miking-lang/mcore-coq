From MCore Require Import Syntax Typing SmallStep Util.
From TLC Require Import LibTactics LibString.

Module Soundness (P : PAT).
  Module S := SmallStep P.
  Import S.

  Module Soundness (PC : PATCHECK) (M : MATCH).
    Module Typing := Typing PC.
    Module SmallStep := SmallStep M.
    Import Typing SmallStep.

    Theorem progress :
      forall t ty,
        ok_term empty_env t ty ->
        is_value t \/ exists t', eval_step t t'.
    Proof.
      introv ttype.
      remember empty_env as Gamma eqn:HGamma.
      induction ttype
        as [ ? ? ? var_in
           | | ? ? ? t1 t2 ttype1 IH1 ? IH2
           | | ? ? ? ty2 t ? IH ].
      - Case "TmVar". rewrite HGamma in var_in. inversion var_in.
      - Case "TmLam". left. apply VLam.
      - Case "TmApp". right. destruct (IH1 HGamma) as [ HV1 | HS1 ].
        + SCase "Val". destruct (IH2 HGamma) as [ HV2 | HS2 ].
          * SSCase "Val". inversion HV1 as [ ? t | ? ? HV ].
            ** S3Case "VLam". exists (tm_subst t t2). apply (EApp HV2).
            ** S3Case "VTyLam". rewrite <- HV in ttype1. inversion ttype1.
          * SSCase "Step". destruct HS2 as [ t' HS ].
            exists (TmApp t1 t'). apply (ECong (CAppR t1 HV1) HS).
        + SCase "Step". destruct HS1 as [ t' HS ].
          exists (TmApp t' t2). apply (ECong (CAppL t2) HS).
      - Case "TmTyLam". left. apply VTyLam.
      - Case "TmTyApp". right. destruct (IH HGamma) as [ HV | HS ].
        + SCase "Val". inversion HV as [ ? ? HV' | ? t' ].
          * SSCase "VLam". rewrite <- HV' in ttype. inversion ttype.
          * SSCase "VTyLam". exists (tm_ty_subst t' ty2). apply ETyApp.
        + SCase "Step". destruct HS as [ t' HS' ].
          exists (TmTyApp t' ty2). apply (ECong (CTyApp ty2) HS').
    Qed.

    Theorem preservation :
      forall Gamma t t' ty,
        ok_term Gamma t ty ->
        eval_step t t' ->
        ok_term Gamma t' ty.
    Proof. Admitted.
  End Soundness.
End Soundness.
