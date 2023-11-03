From TLC Require Import LibString LibNat LibList LibLN.
From MCore Require Import
     Syntax SyntaxProps Typing TypingProps
     SmallStep Tactics.
Import LibListNotation.

Module SmallStepProps (P : PAT).
  Module S := SmallStep P.
  Export S.

  Module SmallStepProps1 (PC : PATCHECK) (M : MATCH).
    Module TP1 := TypingProps1 PC.
    Module S1 := SmallStep1 M.
    Export TP1 S1.

    Module Type MATCHPROPS.
      Parameter matchN_length :
        forall t ps t' i,
          matchN t ps = Some (t', i) -> i < length ps.

      Parameter matchN_Tsubst :
        forall t ps t' i X T,
          matchN t ps = Some (t', i) ->
          matchN (Tsubst_t X T t) ps = Some (Tsubst_t X T t', i).

      Parameter matchN_Ksubst :
        forall t ps t' i X T,
          matchN t ps = Some (t', i) ->
          matchN (Ksubst_t X T t) ps = Some (Ksubst_t X T t', i).

      Parameter matchN_ok_pat :
        forall Gamma ps v v' ty ty' i,
          matchN v ps = Some (v', i) ->
          ok_pat Gamma (nth i ps) ty ty' ->
          Gamma |= v' ~: ty'.

      Parameter exhaustive_has_match :
        forall Gamma ty ps v,
          Gamma |= v ~: ty ->
          pats_exhaustive ps ty ->
          is_value v ->
          exists i v',
            matchN v ps = Some (v', i).
    End MATCHPROPS.

    Module SmallStepProps2 (PCP : PATCHECKPROPS) (MP : MATCHPROPS).
      Module TP2 := TypingProps2 PCP.
      Export MP TP2.

      Lemma get_cases_length :
        forall ps bs t,
          get_cases t = (ps, bs) ->
          length ps = length bs.
      Proof.
        introv Heq. gen ps bs.
        induction t ; intros ; inverts~ Heq.
        destruct (get_cases t1). destruct (get_cases t2).
        inverts H0. rew_listx. fequals~.
      Qed.

      Lemma get_cases_Tsubst :
        forall ps bs X T t,
          get_cases t = (ps, bs) ->
          get_cases (Tsubst_t X T t) = (ps, LibList.map (Tsubst_t X T) bs).
      Proof.
        introv Heq. gen ps bs.
        induction t ; intros ; simpls ; inverts~ Heq.
        destruct (get_cases t1). destruct (get_cases t2).
        destruct (get_cases (Tsubst_t X T t1)). destruct (get_cases (Tsubst_t X T t2)).
        inverts H0. rew_listx. forwards~ Heq1 : IHt1. forwards~ Heq2 : IHt2.
        fequals.
      Qed.

      Lemma Topen_is_value :
        forall i T v,
          is_value (Topen_t i T v) ->
          is_value v.
      Proof.
        introv Hval.
        induction v ; inverts* Hval.
      Qed.

      Lemma is_value_Tsubst :
        forall X T v,
          is_value v ->
          is_value (Tsubst_t X T v).
      Proof.
        introv Hval.
        induction v ; inverts* Hval.
      Qed.

      Lemma push_Tsubst :
        forall f f' X T t1 t2,
          (forall t, Tsubst_t X T (f t) = f' (Tsubst_t X T t)) ->
          is_value t1 ->
          push_value f t1 = t2 ->
          push_value f' (Tsubst_t X T t1) = Tsubst_t X T t2.
      Proof.
        introv Heq Hval Hpush. gen t2.
        induction Hval ; intros ; destruct t2 ; inverts Hpush ;
          simpls ; try rewrite~ Heq.
        - erewrite~ IHHval1. erewrite~ IHHval2.
        - erewrite~ IHHval.
        - erewrite~ IHHval1. erewrite~ IHHval2.
      Qed.

      Lemma step_Tsubst :
        forall X T t1 t2,
          t1 --> t2 ->
          Tsubst_t X (FTName T) t1 --> Tsubst_t X (FTName T) t2.
      Proof.
        introv Hstep.
        induction Hstep ; simpls.
        - rewrite Tsubst_t_open_distr.
          forwards* Hval: is_value_Tsubst H.
        - rewrite* Tsubst_t_topen_distr.
        - rewrite Tsubst_t_open_distr. simpls*.
        - forwards Hval: is_value_Tsubst H. forwards* Hval': is_value_Tsubst H0.
        - forwards Hval: is_value_Tsubst H. forwards* Hval': is_value_Tsubst H0.
        - forwards Hval: is_value_Tsubst H.
          forwards* Hpush: push_Tsubst TmType H. rewrite* <- Hpush.
        - forwards Hval: is_value_Tsubst H.
          forwards* Hpush: push_Tsubst (TmConDef d ty T0) H. rewrite* <- Hpush.
        - apply_fresh ETypeCong. rewrite_all~ Tsubst_t_Topen_comm.
        - apply_fresh EConDefCong. rewrite_all~ Tsubst_t_Kopen_comm.
        - forwards Hval: is_value_Tsubst H. forwards Hval': is_value_Tsubst H0.
          rewrite Tsubst_t_open_distr. rewrite <- nth_map.
          constructors*.
          + apply* get_cases_Tsubst.
          + apply* matchN_Tsubst.
          + rewrite~ lt_peano. rewrite~ <- (get_cases_length ps bs v1).
            apply* matchN_length.
        - inverts H ; simpls* ; forwards* Hval: is_value_Tsubst H0.
      Qed.

      Lemma Topen_step_change :
        forall i T U t1 t2,
          T \notin Tfv_t t1 \u Tfv_t t2 ->
          Topen_t i (FTName T) t1 --> Topen_t i (FTName T) t2 ->
          Topen_t i (FTName U) t1 --> Topen_t i (FTName U) t2.
      Proof.
        introv Hfresh. rewrite_all~ (Tsubst_t_intro T (FTName U)).
        apply step_Tsubst.
      Qed.


      Lemma get_cases_Ksubst :
        forall ps bs X K t,
          get_cases t = (ps, bs) ->
          get_cases (Ksubst_t X K t) = (ps, LibList.map (Ksubst_t X K) bs).
      Proof.
        introv Heq. gen ps bs.
        induction t ; intros ; simpls ; inverts~ Heq.
        destruct (get_cases t1). destruct (get_cases t2).
        destruct (get_cases (Ksubst_t X K t1)). destruct (get_cases (Ksubst_t X K t2)).
        inverts H0. rew_listx. forwards~ Heq1 : IHt1. forwards~ Heq2 : IHt2.
        fequals.
      Qed.

      Lemma Kopen_is_value :
        forall i K v,
          is_value (Kopen_t i K v) ->
          is_value v.
      Proof.
        introv Hval.
        induction v ; inverts* Hval.
      Qed.

      Lemma is_value_Ksubst :
        forall X K v,
          is_value v ->
          is_value (Ksubst_t X K v).
      Proof.
        introv Hval.
        induction v ; inverts* Hval.
      Qed.

      Lemma push_Ksubst :
        forall f f' X T t1 t2,
          (forall t, Ksubst_t X T (f t) = f' (Ksubst_t X T t)) ->
          is_value t1 ->
          push_value f t1 = t2 ->
          push_value f' (Ksubst_t X T t1) = Ksubst_t X T t2.
      Proof.
        introv Heq Hval Hpush. gen t2.
        induction Hval ; intros ; destruct t2 ; inverts Hpush ;
          simpls ; try rewrite~ Heq.
        - erewrite~ IHHval1. erewrite~ IHHval2.
        - erewrite~ IHHval.
        - erewrite~ IHHval1. erewrite~ IHHval2.
      Qed.

      Lemma step_Ksubst :
        forall X K t1 t2,
          t1 --> t2 ->
          Ksubst_t X (FCon K) t1 --> Ksubst_t X (FCon K) t2.
      Proof.
        introv Hstep.
        induction Hstep ; simpls.
        - rewrite Ksubst_t_open_distr.
          forwards* Hval: is_value_Ksubst H.
        - rewrite* Ksubst_t_topen_distr.
        - rewrite Ksubst_t_open_distr. simpls*.
        - forwards Hval: is_value_Ksubst H. forwards* Hval': is_value_Ksubst H0.
        - forwards Hval: is_value_Ksubst H. forwards* Hval': is_value_Ksubst H0.
        - forwards Hval: is_value_Ksubst H.
          forwards* Hpush: push_Ksubst TmType H. rewrite* <- Hpush.
        - forwards Hval: is_value_Ksubst H.
          forwards* Hpush: push_Ksubst (TmConDef d ty T) H. rewrite* <- Hpush.
        - apply_fresh ETypeCong. rewrite_all~ Ksubst_t_Topen_comm.
        - apply_fresh EConDefCong. rewrite_all~ Ksubst_t_Kopen_comm.
        - forwards Hval: is_value_Ksubst H. forwards Hval': is_value_Ksubst H0.
          rewrite Ksubst_t_open_distr. rewrite <- nth_map.
          constructors*.
          + apply* get_cases_Ksubst.
          + apply* matchN_Ksubst.
          + rewrite~ lt_peano. rewrite~ <- (get_cases_length ps bs v1).
            apply* matchN_length.
        - inverts H ; simpls* ; forwards* Hval: is_value_Ksubst H0.
      Qed.

      Lemma Kopen_step_change :
        forall i K U t1 t2,
          K \notin Kfv_t t1 \u Kfv_t t2 ->
          Kopen_t i (FCon K) t1 --> Kopen_t i (FCon K) t2 ->
          Kopen_t i (FCon U) t1 --> Kopen_t i (FCon U) t2.
      Proof.
        introv Hfresh. rewrite_all~ (Ksubst_t_intro K (FCon U)).
        apply step_Ksubst.
      Qed.

      Lemma ok_term_get_cases_eq :
        forall Gamma ty1 ty2 ps ps' bs v,
          Gamma |= v ~: TySem ty1 ty2 ps ->
          is_value v ->
          get_cases v = (ps', bs) ->
          ps' = ps.
      Proof.
        introv Htype Hval Heq. gen ps ps' bs.
        induction Hval ; intros ; inverts Htype ; simpls.
        - inverts~ Heq.
        - destruct (get_cases v1). destruct (get_cases v2).
          inverts Heq. fequals*.
      Qed.

      Lemma ok_term_get_cases_inv :
        forall Gamma ty1 ty2 ps ps' bs v i,
          Gamma |= v ~: TySem ty1 ty2 ps ->
          is_value v ->
          get_cases v = (ps', bs) ->
          i < length ps' ->
          exists L ty1',
            ok_pat Gamma (nth i ps') ty1 ty1' /\
              (forall x, x \notin L ->
                    Gamma & x ~ BindVar ty1' |= [0 ~> TmFVar x] nth i bs ~: ty2).
      Proof.
        introv Htype Hval Heq. gen ps ps' bs i.
        induction Hval ; intros ; inverts Htype ; simpls.
        - inverts Heq. rew_list in H. assert (i = 0) by nat_math. substs*.
        - destruct (get_cases v1) eqn:Heq1. destruct (get_cases v2).
          inverts Heq. rew_list in H. rewrite_all nth_app. rewrite~ <- (get_cases_length l l0 v1).
          rewrite_all lt_peano. case_if.
          + forwards* Hleft : IHHval1.
          + forwards* Hright : IHHval2. nat_math.
      Qed.

      Lemma ok_term_Topen_push :
        forall T Gamma t ty,
          is_value t ->
          T \notin dom Gamma \u Tfv_t t \u Tfv_ty ty ->
          Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty ->
          Gamma |= push_value TmType t ~: ty.
      Proof with eauto with mcore.
        introv Hval Hfresh Htype. gen ty.
        induction Hval ; intros ; inverts Htype ; simpls.
        { Case "TmLam". rewrite notin_Topen_ty in *...
          assert (Gamma |= ty ~:: KiType)
            by (apply_empty~ (ok_type_tname_strengthening T) ; apply* ok_env_push).
          apply_fresh* TLam as x. apply_fresh TType as T'...
          applys~ ok_term_Topen_change T.
          - rewrite notin_union. rewrite~ open_notin_T.
          - rewrite* Topen_t_open_comm. apply_empty ok_term_comm... }
        { Case "TmTyLam". rewrite notin_Topen_k in *...
          assert (ok_kind Gamma k) by apply_empty~ (ok_kind_tname_strengthening T).
          apply_fresh* TTyLam as X. apply_fresh TType as T'...
          applys~ ok_term_Topen_change T.
          - rewrite notin_union. rewrite topen_t_notin_T. rewrite topen_notin_T ; simpls~.
          - rewrite* Topen_t_topen_comm. apply_empty~ ok_term_comm.
            constructor~. constructor~. apply* ok_env_push. }
        { Case "TmProd". constructor~. }
        { Case "TmCon". rewrite notin_Topen_ty in *...
          constructors.
          + binds_cases H2...
          + apply_empty (ok_type_tname_strengthening T) ; auto ; apply* ok_env_push.
          + apply_empty (ok_type_tname_strengthening T) ; auto ; apply* ok_env_push.
          + apply~ IHHval. assert (T \notin Tfv_ty ({0 ~> ty} ty1))...
            rewrite~ topen_notin_T. binds_cases H2.
            forwards (L'&?&?&?&Htk&?): ok_env_binds_con_inv B. apply* ok_env_push.
            pick_fresh X. forwards~ Hnin: ok_type_notin_T T (Htk X).
            rewrite topen_notin_T in Hnin ; simpls~. }
        { Case "TmSem". rewrite notin_Topen_ty in *...
          assert (Gamma |= ty ~:: KiType)
            by (apply_empty~ (ok_type_tname_strengthening T) ; apply* ok_env_push).
          apply_fresh* TSem as x.
          - apply_empty* (ok_pat_tname_strengthening T).
          - apply_fresh TType as T'... applys~ ok_term_Topen_change T.
            + rewrite notin_union. rewrite~ open_notin_T.
            + rewrite* Topen_t_open_comm. apply_empty~ ok_term_comm.
              constructor~. constructor~. apply* ok_env_push.
              applys ok_pat_ok_type.
              apply_empty* (ok_pat_tname_strengthening T) ; auto. }
        { Case "TmComp". constructor~. apply IHHval1 ; simpls~. apply IHHval2 ; simpls~. }
      Qed.

      Lemma ok_term_Kopen_push :
        forall K Gamma d ty' T t ty,
          is_value t ->
          K \notin dom Gamma \u Kfv_t t \u Kfv_ty ty ->
          Gamma & K ~ BindCon d ty' T |= Kopen_t 0 (FCon K) t ~: ty ->
          Gamma |= push_value (TmConDef d ty' T) t ~: ty.
      Proof with eauto with mcore.
        introv Hval Hfresh Htype. gen ty.
        induction Hval ; intros ;
          forwards Henv : ok_term_ok_env Htype ;
          forwards (L0 & T' & Heq & Hd & Htk & HT): ok_env_con_inv Henv ;
          inverts Htype ; substs ; simpls.
        { Case "TmLam". rewrite notin_Kopen_ty in *...
          assert (Gamma |= ty ~:: KiType)
            by (apply_empty~ (ok_type_con_strengthening K) ; eauto ; apply* ok_env_push).
          assert (Hty' : forall x X,
                     X \notin L0 \u dom Gamma \u \{x} ->
                     x # Gamma ->
                     Gamma & x ~ BindVar ty & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X} ty' ~:: KiType).
          { introv Hnin Hfr. forwards~ Htk' : Htk X. apply~ ok_type_weakening.
            constructor*. constructor~. apply_empty~ ok_data_weakening. constructor*. }
          apply_fresh* TLam as x. apply_fresh TConDef as K'...
          - apply_empty ok_data_weakening...
          - applys~ ok_term_Kopen_change K.
            + rewrite notin_union. rewrite~ open_notin_K.
            + rewrite* Kopen_t_open_comm. apply_empty~ ok_term_comm.
              apply_fresh EnvCon as X... apply_empty~ ok_data_weakening. constructor... }
        { Case "TmTyLam". rewrite notin_Kopen_k in *...
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
          apply_fresh* TTyLam as X. apply_fresh TConDef as K'...
          - apply_empty ok_data_weakening...
          - rewrite~ Heq'.
          - rewrite Heq'. applys~ ok_term_Kopen_change K.
            + rewrite notin_union. rewrite topen_t_notin_K. rewrite topen_notin_K ; simpls~.
            + rewrite* Kopen_t_topen_comm. apply_empty~ ok_term_comm.
              apply_fresh EnvCon as X... apply_empty~ ok_data_weakening. constructor... }
        { Case "TmProd". constructor~. }
        { Case "TmCon". rewrite notin_Kopen_ty in *...
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
          + apply~ IHHval. assert (K \notin Kfv_ty ({0 ~> ty} ty1))...
            rewrite~ topen_notin_K. binds_cases H2.
            forwards (L'&?&?&?&Htk'&?): ok_env_binds_con_inv B. apply* ok_env_push.
            pick_fresh X. forwards~ Hnin': ok_type_notin_K K (Htk' X).
            rewrite~ topen_notin_K in Hnin'. simpls~. }
        { Case "TmSem". rewrite notin_Kopen_ty in *...
          assert (Gamma |= ty ~:: KiType)
            by (apply_empty~ (ok_type_con_strengthening K) ; eauto ; apply* ok_env_push).
          assert (Gamma |= ty1' ~:: KiType)
            by (applys ok_pat_ok_type ; apply_empty* (ok_pat_con_strengthening K) ; auto).
          assert (Hty' : forall x X,
                     X \notin L0 \u dom Gamma \u \{x} ->
                     x # Gamma ->
                     Gamma & x ~ BindVar ty1' & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X} ty' ~:: KiType).
          { introv Hnin Hfr. forwards~ Htk' : Htk X. apply~ ok_type_weakening.
            constructor*. constructor~. apply_empty~ ok_data_weakening. constructor*. }
          apply_fresh* TSem as x.
          - apply_empty* (ok_pat_con_strengthening K).
          - apply_fresh TConDef as T'...
            + apply_empty~ ok_data_weakening. constructor~. apply* ok_env_concat.
            + applys~ ok_term_Kopen_change K.
              * rewrite notin_union. rewrite~ open_notin_K.
              * rewrite* Kopen_t_open_comm. apply_empty~ ok_term_comm.
                constructors... apply_empty~ ok_data_weakening. constructor~. apply* ok_env_concat. }
        { Case "TmComp". constructor~. apply IHHval1 ; simpls~. apply IHHval2 ; simpls~. }
      Qed.

    End SmallStepProps2.
  End SmallStepProps1.
End SmallStepProps.
