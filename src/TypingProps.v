From TLC Require Import LibString LibList LibLN.
From MCore Require Import Syntax SyntaxProps Typing Tactics.
Import LibListNotation.

(**************************)
(** PROPERTIES OF TYPING **)
(**************************)

Module TypingProps (P : PAT).
  Module T := Typing P.
  Export T.

  Module TypingProps1 (PC : PATCHECK).
    Module T1 := Typing1 PC.
    Export T1.

    Module Type PATCHECKPROPS.
      Parameter ok_pat_lcp :
        forall Gamma p T T',
          ok_pat Gamma p T T' ->
          lcp p.

      Parameter ok_pat_ok_type :
        forall Gamma p T T',
          ok_pat Gamma p T T' ->
          ok_env Gamma ->
          Gamma |= T' ~:: KiType.

      Parameter ok_pat_weakening :
        forall G3 G1 G2 p T T',
          ok_pat (G1 & G3) p T T' ->
          ok_env (G1 & G2 & G3) ->
          ok_pat (G1 & G2 & G3) p T T'.

      Parameter exhaustive_weakening :
        forall G3 G1 G2 ps T,
          exhaustive (G1 & G3) ps T ->
          ok_env (G1 & G2 & G3) ->
          exhaustive (G1 & G2 & G3) ps T.

      Parameter contradictory_weakening :
        forall G3 G1 G2,
          contradictory (G1 & G3) ->
          ok_env (G1 & G2 & G3) ->
          contradictory (G1 & G2 & G3).

      Parameter ok_pat_strengthening :
        forall G1 G2 x p T1 T1' T2,
          ok_pat (G1 & x ~ BindVar T2 & G2) p T1 T1' ->
          ok_pat (G1 & G2) p T1 T1'.

      Parameter ok_pat_bsubst :
        forall G1 G2 p x t T T',
          ok_pat (G1 & G2) p T T' ->
          ok_pat (G1 & map (bsubst x t) G2) p T T'.

      Parameter exhaustive_strengthening :
        forall G1 G2 x ps T1 T2,
          exhaustive (G1 & x ~ BindVar T2 & G2) ps T1 ->
          exhaustive (G1 & G2) ps T1.

      Parameter exhaustive_bsubst :
        forall G1 G2 x t ps T1,
          exhaustive (G1 & G2) ps T1 ->
          exhaustive (G1 & map (bsubst x t) G2) ps T1.

      Parameter contradictory_subst :
        forall G1 G2 x u T,
          contradictory (G1 & x ~ BindVar T & G2) ->
          is_value u ->
          G1 |= u ~: T ->
          contradictory (G1 & map (bsubst x u) G2).

      Parameter ok_pat_match_strengthening :
        forall M G2 G1 t p' m ty ty' p,
          ok_pat (G1 & M ~ BindMatch t p' m & G2) p ty ty' ->
          ok_pat (G1 & G2) p ty ty'.

      Parameter exhaustive_match_strengthening :
        forall M G2 G1 t p' m ty ps,
          exhaustive (G1 & M ~ BindMatch t p' m & G2) ps ty ->
          exhaustive (G1 & G2) ps ty.

      Parameter ok_pat_tsubst :
        forall G1 G2 p X U T T' k,
          ok_pat (G1 & X ~ BindTVar k & G2) p T T' ->
          G1 |= U ~:: k ->
          ok_pat (G1 & map (tbsubst X U) G2) p ({X => U}T) ({X => U}T').

      Parameter exhaustive_tsubst :
        forall G1 G2 ps X U ty k,
          exhaustive (G1 & X ~ BindTVar k & G2) ps ty ->
          G1 |= U ~:: k ->
          exhaustive (G1 & map (tbsubst X U) G2) ps ({X => U} ty).

      Parameter contradictory_tsubst :
        forall G1 G2 X U k,
          contradictory (G1 & X ~ BindTVar k & G2) ->
          G1 |= U ~:: k ->
          contradictory (G1 & map (tbsubst X U) G2).

      Parameter ok_pat_comm :
        forall G1 G2 x1 x2 b1 b2 p T T',
          ok_pat (G1 & x1 ~ b1 & x2 ~ b2 & G2) p T T' ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          ok_pat (G1 & x2 ~ b2 & x1 ~ b1 & G2) p T T'.

      Parameter exhaustive_comm :
        forall G1 G2 x1 x2 b1 b2 ps T,
          exhaustive (G1 & x1 ~ b1 & x2 ~ b2 & G2) ps T ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          exhaustive (G1 & x2 ~ b2 & x1 ~ b1 & G2) ps T.

      Parameter contradictory_comm :
        forall G1 G2 x1 x2 b1 b2,
          contradictory (G1 & x1 ~ b1 & x2 ~ b2 & G2) ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          contradictory (G1 & x2 ~ b2 & x1 ~ b1 & G2).

      Parameter ok_pat_tname_strengthening :
        forall T G2 G1 ty ty' p,
          T \notin Tfv_ty ty ->
          ok_pat (G1 & T ~ BindTName & G2) p ty ty' ->
          ok_env (G1 & G2) ->
          ok_pat (G1 & G2) p ty ty'.

      Parameter contradictory_tname_strengthening :
        forall T G2 G1,
          contradictory (G1 & T ~ BindTName & G2) ->
          ok_env (G1 & G2) ->
          contradictory (G1 & G2).

      Parameter ok_pat_Tsubst :
        forall G2 G1 T T' p ty ty',
          ok_pat (G1 & T ~ BindTName & G2) p ty ty' ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_env (G1 & T ~ BindTName & G2) ->
          ok_pat (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2)
                 p (Tsubst_ty T (FTName T') ty) (Tsubst_ty T (FTName T') ty').

      Parameter exhaustive_Tsubst :
        forall G1 G2 ps T T' ty,
          exhaustive (G1 & T ~ BindTName & G2) ps ty ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_env (G1 & T ~ BindTName & G2) ->
          exhaustive (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2)
                          ps (Tsubst_ty T (FTName T') ty).

      Parameter contradictory_Tsubst :
        forall G1 G2 T T',
          contradictory (G1 & T ~ BindTName & G2) ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_env (G1 & T ~ BindTName & G2) ->
          contradictory (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2).

      Parameter ok_pat_con_strengthening :
        forall K G2 G1 d0 ty0 T ty ty' p,
          K \notin Kfv_ty ty ->
          ok_pat (G1 & K ~ BindCon d0 ty0 T & G2) p ty ty' ->
          ok_env (G1 & G2) ->
          ok_pat (G1 & G2) p ty ty'.

      Parameter contradictory_con_strengthening :
        forall K G2 G1 d0 ty0 T,
          contradictory (G1 & K ~ BindCon d0 ty0 T & G2) ->
          ok_env (G1 & G2) ->
          contradictory (G1 & G2).

      Parameter ok_pat_notin_K :
        forall Gamma p ty ty' X,
          ok_pat Gamma p ty ty' ->
          X # Gamma ->
          X \notin Kfv_p p.

      Parameter ok_pat_Ksubst :
        forall G2 G1 K K' d0 ty0 T p ty ty',
          ok_pat (G1 & K ~ BindCon d0 ty0 T & G2) p ty ty' ->
          K' # G1 & K ~ BindCon d0 ty0 T & G2 ->
          ok_env (G1 & K ~ BindCon d0 ty0 T & G2) ->
          ok_pat (G1 & K' ~ BindCon d0 ty0 T & map (Kbsubst K (FCon K')) G2)
                 (Ksubst_p K (FCon K') p) (Ksubst_ty K (FCon K') ty) (Ksubst_ty K (FCon K') ty').

      Parameter compatible_Ksubst :
        forall ps K K',
          K' \notin fold varsM Kfv_p ps ->
          compatible ps ->
          compatible (LibList.map (Ksubst_p K (FCon K')) ps).

      Parameter exhaustive_Ksubst :
        forall G1 G2 ps K K' d ty' T ty,
          exhaustive (G1 & K ~ BindCon d ty' T & G2) ps ty ->
          K' # G1 & K ~ BindCon d ty' T & G2 ->
          ok_env (G1 & K ~ BindCon d ty' T & G2) ->
          exhaustive (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2)
                          (LibList.map (Ksubst_p K (FCon K')) ps) (Ksubst_ty K (FCon K') ty).

      Parameter contradictory_Ksubst :
        forall G1 G2 K K' d ty' T,
          contradictory (G1 & K ~ BindCon d ty' T & G2) ->
          K' # G1 & K ~ BindCon d ty' T & G2 ->
          ok_env (G1 & K ~ BindCon d ty' T & G2) ->
          contradictory (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2).

    End PATCHECKPROPS.

    Module TypingProps2 (PP : PATPROPS) (PCP : PATCHECKPROPS).
      Module SP1 := SyntaxProps1 PP.
      Export PCP SP1.

      Lemma ok_env_ok :
        forall Gamma,
          ok_env Gamma ->
          ok Gamma.
      Proof. introv Henv ; induction* Henv. Qed.
      #[export]
       Hint Resolve ok_env_ok : mcore.

      Lemma ok_env_concat :
        forall G1 G2,
          ok_env (G1 & G2) ->
          ok_env G1.
      Proof with eauto.
        introv Henv.
        induction G2 using env_ind.
        { Case "Empty". rew_env_concat in *... }
        { Case "Push". apply IHG2. rew_env_concat in *.
          inverts Henv ;
            try (apply eq_push_inv in H; inverts H as []; substs~).
          false. apply *empty_push_inv. }
      Qed.

      Lemma ok_type_ok_env :
        forall Gamma T k,
          Gamma |= T ~:: k ->
          ok_env Gamma.
      Proof.
        introv hasType.
        induction* hasType ; pick_fresh_gen L x; eauto using ok_env_concat.
      Qed.
      #[export]
       Hint Resolve ok_type_ok_env : mcore.

      Lemma ok_term_ok_env :
        forall Gamma t T,
          Gamma |= t ~: T ->
          ok_env Gamma.
      Proof.
        introv hasType.
        induction* hasType; pick_fresh_gen L x; eauto using ok_env_concat.
      Qed.
      #[export]
       Hint Resolve ok_term_ok_env : mcore.

      Lemma ok_data_weakening :
        forall G3 G1 G2 d,
          ok_data (G1 & G3) d ->
          ok_env  (G1 & G2 & G3) ->
          ok_data (G1 & G2 & G3) d.
      Proof.
        introv Hd Henv.
        remember (G1 & G3) as Gamma eqn:HGamma.
        assert (Hok : ok (G1 & G2)) by applys* ok_concat_inv_l G3.
        induction Hd ; constructor*.
        - substs ; apply* binds_weaken.
        - induction H1 ; substs ; constructors*.
          apply* binds_weaken.
      Qed.

      Lemma ok_kind_weakening :
        forall G3 G1 G2 k,
          ok_kind (G1 & G3) k ->
          ok_env  (G1 & G2 & G3) ->
          ok_kind (G1 & G2 & G3) k.
      Proof.
        introv Hk.
        remember (G1 & G3) as Gamma eqn:HGamma.
        destruct Hk; subst*. constructor. apply* ok_data_weakening.
      Qed.

      Lemma ok_type_weakening :
        forall G3 G1 G2 T k,
          G1 & G3 |= T ~:: k ->
          ok_env (G1 & G2 & G3) ->
          G1 & G2 & G3 |= T ~:: k.
      Proof with eauto using ok_kind_weakening, ok_data_weakening with mcore.
        introv Htk Henv.
        remember (G1 & G3) as Gamma. gen G3.
        induction Htk; intros; substs...
        { Case "TyFVar". constructor~. apply* binds_weaken. }
        { Case "TyAll". apply_fresh KAll...
          apply_ih_bind H1 ; auto. constructor... }
        { Case "TySem". constructor~.
          apply* Forall_pred_incl. intros p (ty1' & Hwf).
          eexists. apply* ok_pat_weakening. }
      Qed.

      Lemma ok_term_weakening :
        forall G3 G2 G1 t T,
          G1 & G3 |= t ~: T ->
          ok_env (G1 & G2 & G3) ->
          G1 & G2 & G3 |= t ~: T.
      Proof with eauto using ok_type_weakening, ok_kind_weakening, ok_data_weakening with mcore.
        introv hasType Henv. remember (G1 & G3) as H. gen G3.
        induction hasType; intros; substs...
        { Case "TmFVar". constructors~. apply* binds_weaken. }
        { Case "TmLam". apply_fresh* TLam as y...
          apply_ih_bind H1 ; auto. constructor... }
        { Case "TmTyLam". apply_fresh* TTyLam as X...
          apply_ih_bind H1 ; auto. constructor... }
        { Case "TmCon". constructors...
          apply* binds_weaken. }
        { Case "TmMatch". apply_fresh TMatch ; intros...
          - apply* ok_pat_weakening.
          - do_rew_2 concat_assoc (applys H1 M) ; auto. easy.
            constructor~.
            + constructors~. apply* ok_pat_weakening.
            + apply_empty ok_type_weakening.
              * apply~ ok_type_weakening. apply* ok_pat_ok_type.
              * constructors~. apply* ok_pat_weakening.
          - apply_ih_bind (H3 y) ; auto.
            constructors~. apply* ok_pat_weakening. }
        { Case "TmNever". constructor... apply* contradictory_weakening. }
        { Case "TmType". apply_fresh TType as T...
          apply_ih_bind H0 ; auto. constructor... }
        { Case "TmConDef". apply_fresh TConDef as K...
          - apply_ih_bind ok_type_weakening ; auto. constructor...
          - apply* binds_weaken.
          - apply_ih_bind H3 ; auto.
            apply_fresh EnvCon as X...
            + apply_ih_bind ok_type_weakening ; auto. constructor...
            + apply* binds_weaken. }
        { Case "TmSem". apply_fresh* TSem as y... apply* ok_pat_weakening.
          apply_ih_bind H2 ; auto. constructor...
          apply~ ok_type_weakening. apply* ok_pat_ok_type. }
        { Case "TmSemApp". constructors~. apply~ exhaustive_weakening. }
      Qed.

      Lemma ok_env_con_inv :
        forall Gamma K d ty T,
          ok_env (Gamma & K ~ BindCon d ty T) ->
          exists L T',
            T = FTName T'
            /\ ok_data Gamma d
            /\ (forall X, X \notin L -> Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty ~:: KiType)
            /\ binds T' BindTName Gamma.
      Proof.
        introv Henv.
        inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?)) ; try discriminate.
        - false. apply* empty_push_inv.
        - substs ; inverts* H5. exists* L T0.
      Qed.

      Lemma ok_env_tvar_inv :
        forall Gamma X k,
          ok_env (Gamma & X ~ BindTVar k) ->
          ok_kind Gamma k.
      Proof.
        introv Henv.
        inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; fequals).
        false. apply* empty_push_inv.
      Qed.

      Lemma ok_env_var_inv :
        forall Gamma x T,
          ok_env (Gamma & x ~ BindVar T) ->
          Gamma |= T ~:: KiType.
      Proof.
        introv Henv.
        inverts Henv ; try (apply eq_push_inv in H as (? & ? & ?); substs* ; fequals).
        false. apply* empty_push_inv.
      Qed.

      Lemma ok_env_binds_con_inv :
        forall Gamma K d ty T,
          ok_env Gamma  ->
          binds K (BindCon d ty T) Gamma ->
          exists L T',
            T = FTName T'
            /\ ok_data Gamma d
            /\ (forall X, X \notin L -> Gamma & X ~ BindTVar (KiData d) |= {0 ~> TyFVar X}ty ~:: KiType)
            /\ binds T' BindTName Gamma.
      Proof.
        introv Henv Hbinds.
        induction Gamma using env_ind.
        - false. apply* binds_empty_inv.
        - binds_cases Hbinds.
          + destruct~ IHGamma as (L & T' & Heq & Hd & Htk & Hbinds'). apply* ok_env_concat.
            exists (L \u dom Gamma \u \{x}) T'. splits*. apply_empty~ ok_data_weakening.
            introv Hfresh. apply~ ok_type_weakening. constructor~. constructor.
            apply_empty~ ok_data_weakening. apply* binds_concat_left_ok.
          + inverts EQ. forwards* (L & T' & Heq & Hd & Htk & Hbinds') : ok_env_con_inv.
            exists (L \u dom Gamma \u \{K}) T'. splits~. apply_empty~ ok_data_weakening.
            introv Hfresh. apply~ ok_type_weakening. constructor~. constructor.
            apply_empty~ ok_data_weakening. apply* binds_concat_left_ok.
      Qed.

      Lemma ok_env_binds_tvar_inv :
        forall Gamma X k,
          ok_env Gamma ->
          binds X (BindTVar k) Gamma ->
          ok_kind Gamma k.
      Proof.
        introv Henv Hbinds.
        induction Gamma using env_ind.
        - false. apply* binds_empty_inv.
        - binds_cases Hbinds.
          + apply_empty~ ok_kind_weakening. apply~ IHGamma. apply* ok_env_concat.
          + substs. forwards* Hk: ok_env_tvar_inv. apply_empty~ ok_kind_weakening.
      Qed.

      Lemma ok_env_binds_var_inv :
        forall Gamma x ty,
          ok_env Gamma ->
          binds x (BindVar ty) Gamma ->
          Gamma |= ty ~:: KiType.
      Proof.
        introv Henv Hbinds.
        induction Gamma using env_ind.
          - false. apply* binds_empty_inv.
          - binds_cases Hbinds.
            + apply_empty~ ok_type_weakening. forwards~ ?: ok_env_concat Henv.
            + inverts EQ. apply_empty~ ok_type_weakening. apply* ok_env_var_inv.
      Qed.

      Lemma ok_data_lcd : forall Gamma d, ok_data Gamma d -> lcd d.
      Proof.
        introv Hd. unfolds.
        induction Hd ; rew_listx*. splits*. splits*.
        induction H1 ; rew_listx*.
      Qed.
      #[export]
       Hint Resolve ok_data_lcd : mcore.

      Lemma ok_kind_lck : forall Gamma k, ok_kind Gamma k -> lck k.
      Proof. introv Hk. destruct* Hk. Qed.
      #[export]
       Hint Resolve ok_kind_lck : mcore.

      Lemma ok_type_lct :
        forall Gamma T k,
          Gamma |= T ~:: k ->
          lct T.
      Proof.
        introv Htk ; induction* Htk.
        - constructor~. apply* Forall_pred_incl.
          intros p (ty1' & Hwf). apply* ok_pat_lcp.
      Qed.
      #[export]
       Hint Resolve ok_type_lct : mcore.

      Lemma ok_term_lct :
        forall Gamma t T,
          Gamma |= t ~: T ->
          lct T.
      Proof with eauto using ok_env_binds_var_inv, ok_type_lct.
        introv hasType.
        induction* hasType...
        { Case "TmLam". constructors...
          pick_fresh_gen L y... }
        { Case "TmApp". inverts* IHhasType1. }
        { Case "TmTyLam". inverts* IHhasType.
          assert(Hlct: lct ty2)...
          pick_fresh X. rewrite *(tsubst_intro X).
          apply* tsubst_lct. }
        { Case "TmFix". inverts* IHhasType. }
        { Case "TmProj1". inverts* IHhasType. }
        { Case "TmProj2". inverts* IHhasType. }
        { Case "TmMatch". pick_fresh_gen L y... }
        { Case "TmType". pick_fresh T. applys~ H0 T. }
        { Case "TmConDef". pick_fresh K. applys~ H3 K. }
        { Case "TmSem". constructors...
          pick_fresh_gen L y... forwards* Hpat : ok_pat_lcp. }
        { Case "TmComp". inverts IHhasType1. inverts IHhasType2. constructor~. rew_listx~. }
        { Case "TmSemApp". inverts* IHhasType1. }
      Qed.
      #[export]
       Hint Resolve ok_term_lct : mcore.

      Lemma ok_term_lc :
        forall Gamma t T,
          Gamma |= t ~: T ->
          lc t.
      Proof.
        introv Htype; induction* Htype.
        - pick_fresh_gen L y. forwards* Hpat : ok_pat_lcp.
        - forwards* Hpat : ok_pat_lcp.
      Qed.
      #[export]
       Hint Resolve ok_term_lc : mcore.

      Lemma ok_type_ok_kind :
        forall Gamma T k,
          Gamma |= T ~:: k ->
          ok_kind Gamma k.
      Proof. introv Htk. induction* Htk. apply* ok_env_binds_tvar_inv. Qed.

      Lemma ok_data_notin_T :
        forall Gamma d X,
          ok_data Gamma d ->
          X # Gamma ->
          X \notin Tfv_d d.
      Proof.
        introv Hd Hfresh. unfolds Tfv_d.
        induction Hd ; rew_listx ; simpls~.
        rewrite notin_union. splits*.
        - rewrite notin_singleton. intro. substs.
          forwards~ Hin : get_some_inv H0.
      Qed.

      Lemma ok_kind_notin_T :
        forall Gamma k X,
          ok_kind Gamma k ->
          X # Gamma ->
          X \notin Tfv_k k.
      Proof.
        introv Hk Hfresh. unfolds Tfv_k.
        destruct~ Hk. apply* ok_data_notin_T.
      Qed.

      Lemma assoc_data_in :
        forall d T Ks,
          mem (FTName T, Ks) d -> T \in Tfv_d d.
      Proof.
        introv Hassoc. unfolds Tfv_d.
        induction Hassoc ; rew_listx ; simpls~.
        - rewrite~ in_union. rewrite~ in_singleton.
        - destruct y. rewrite~ in_union.
      Qed.

      Lemma ok_type_notin_T :
        forall Gamma T k X,
          Gamma |= T ~:: k ->
          X # Gamma ->
          X \notin Tfv_ty T.
      Proof with eauto using ok_data_notin_T, ok_kind_notin_T.
        introv Htk Hfresh.
        induction Htk; simpls...
        { Case "TyAll". rewrite notin_union. splits...
          pick_fresh Y. forwards~ Htk: H1 Y.
          rewrite topen_notin_T in Htk ; simpls~. }
        { Case "TyCon". rewrite notin_union. splits~.
          forwards Hk: ok_type_ok_kind Htk.
          forwards~ Hnin : ok_kind_notin_T X Hk.
          assert (X <> T) by (intro ; substs ; apply Hnin ; applys* assoc_data_in).
          auto. }
      Qed.

      Lemma ok_term_notin_T :
        forall Gamma t T X,
          Gamma |= t ~: T ->
          X # Gamma ->
          X \notin Tfv_t t.
      Proof with eauto using ok_data_notin_T, ok_kind_notin_T, ok_type_notin_T.
        introv Htype Hfresh.
        induction Htype; simpls ; rewrite_all notin_union...
        - pick_fresh x. forwards~ Hnin : H1 x. rewrite open_notin_T in Hnin...
        - pick_fresh Y. forwards~ Hnin : H1 Y. rewrite topen_t_notin_T in Hnin...
        - pick_fresh M. pick_fresh x. forwards~ Hnin1 : H1 M x.
          forwards~ Hnin2 : H3 M. rewrite open_notin_T in Hnin1...
        - pick_fresh T. forwards~ Hnin : Topen_t_notin_T (H0 T).
        - pick_fresh K. forwards~ Hnin1 : Kopen_t_notin_T (H3 K).
          forwards~ Hnin2 : ok_type_notin_T X (H0 K).
          rewrite topen_notin_T in Hnin2 ; simpls~.
          assert (X <> T)... intro ; substs. forwards~ ?: get_some_inv H1.
        - pick_fresh x. forwards~ Hnin : H2 x. rewrite open_notin_T in Hnin...
      Qed.

      Lemma data_sub_notin_T :
        forall T d1 d2,
          T \notin Tfv_d d1 ->
          data_sub d2 d1 ->
          T \notin Tfv_d d2.
      Proof with eauto.
        introv Hnin Hsub. unfolds data_sub. unfolds Tfv_d.
        induction d2 ; rew_listx ; simpls~.
        rewrite notin_union ; split~. destruct a. destruct~ t.
        assert (T <> v)... intro ; substs.
        forwards~ (?&Hmem&?) : Hsub. forwards~ (?&?&Heq) : mem_inv_middle Hmem.
        substs. rew_listx* in Hnin. simpls.
        notin_false.
      Qed.

      Lemma ok_data_notin_K :
        forall Gamma d X,
          ok_data Gamma d ->
          X # Gamma ->
          X \notin Kfv_d d.
      Proof.
        introv Hd Hfresh. unfolds Kfv_d.
        induction Hd ; rew_listx ; simpls~.
        rewrite notin_union. splits*.
        induction H1 ; rew_listx ; simpls~ ; rewrite notin_union ; splits~.
        - rewrite notin_singleton. intro. substs.
          forwards~ Hin : get_some_inv H3.
      Qed.

      Lemma ok_kind_notin_K :
        forall Gamma k X,
          ok_kind Gamma k ->
          X # Gamma ->
          X \notin Kfv_k k.
      Proof.
        introv Hk Hfresh. unfolds Kfv_k.
        destruct~ Hk. apply* ok_data_notin_K.
      Qed.

      Lemma ok_type_notin_K :
        forall Gamma T k X,
          Gamma |= T ~:: k ->
          X # Gamma ->
          X \notin Kfv_ty T.
      Proof with eauto using ok_data_notin_K, ok_kind_notin_K, ok_pat_notin_K.
        introv Htk Hfresh.
        induction Htk; simpls...
        { Case "TyAll". rewrite notin_union. splits...
          pick_fresh Y. forwards~ Htk: H1 Y.
          rewrite topen_notin_K in Htk ; simpls~. }
        { Case "TySem". rewrite_all notin_union. repeat split~.
          induction ps ; rew_listx ; simpls~. rew_listx in H. destruct H as ((ty1'&Hfw)&?).
          rewrite notin_union... }
      Qed.

      Lemma ok_term_notin_K :
        forall Gamma t T X,
          Gamma |= t ~: T ->
          X # Gamma ->
          X \notin Kfv_t t.
      Proof with eauto using ok_data_notin_K, ok_kind_notin_K, ok_type_notin_K, ok_pat_notin_K.
        introv Htype Hfresh.
        induction Htype; simpls ; rewrite_all notin_union...
        - pick_fresh x. forwards~ Hnin : H1 x. rewrite open_notin_K in Hnin...
        - pick_fresh Y. forwards~ Hnin : H1 Y. rewrite topen_t_notin_K in Hnin...
        - assert (X <> K)... intro ; substs. forwards~ ?: get_some_inv H.
        - pick_fresh M. pick_fresh x. forwards~ Hnin1 : H1 M x.
          forwards~ Hnin2 : H3 M. rewrite open_notin_K in Hnin1...
        - pick_fresh T. forwards~ Hnin : Topen_t_notin_K (H0 T).
        - pick_fresh K0. forwards~ Hnin1 : Kopen_t_notin_K (H3 K0).
          forwards~ Hnin2 : ok_type_notin_K X (H0 K0).
          rewrite topen_notin_K in Hnin2 ; simpls...
        - pick_fresh x. forwards~ Hnin1 : H2 x. rewrite open_notin_K in Hnin1...
      Qed.

      Lemma data_sub_notin_K :
        forall K d1 d2,
          K \notin Kfv_d d1 ->
          data_sub d2 d1 ->
          K \notin Kfv_d d2.
      Proof with eauto.
        introv Hnin Hsub. unfolds data_sub. unfolds Kfv_d.
        induction d2 ; rew_listx ; simpls~.
        rewrite notin_union ; split~. destruct a.
        forwards* (Ks'&Hmem&HsubK) : Hsub.
        forwards~ (?&?&Heq) : mem_inv_middle Hmem. substs.
        rew_listx* in Hnin ; simpls.
        assert (HninK : K \notin fold varsM (fun K => Kfv K) Ks')...
        clears IHd2 Hsub Hnin Hmem.
        induction l ; rew_listx ; simpls~.
        rewrite notin_union ; split~. destruct~ a.
        assert (K <> v)... intro ; substs.
        forwards~ Hmem : HsubK.
        forwards~ (?&?&Heq) : mem_inv_middle Hmem. substs.
        rew_listx* in HninK. simpls. notin_false.
      Qed.

      Lemma ok_data_strengthening :
        forall G1 G2 x T d,
          ok_data (G1 & x ~ BindVar T & G2) d ->
          ok_data (G1 & G2) d.
      Proof.
        introv Hd.
        remember (G1 & x ~ BindVar T & G2) as Gamma.
        induction Hd ; constructor*.
        - substs ; binds_cases H0 ; auto.
        - induction* H1 ; substs ; constructors*.
          binds_cases H3 ; eauto.
      Qed.

      Lemma ok_kind_strengthening :
        forall G1 G2 x T k,
          ok_kind (G1 & x ~ BindVar T & G2) k ->
          ok_kind (G1 & G2) k.
      Proof.
        introv Hk. remember (G1 & x ~ BindVar T & G2) as G.
        destruct Hk ; substs*. constructor. apply* ok_data_strengthening.
      Qed.

      Lemma ok_type_strengthening :
        forall G2 G1 x T1 T2 k,
          G1 & x ~ BindVar T2 & G2 |= T1 ~:: k ->
          ok_env (G1 & G2) ->
          G1 & G2 |= T1 ~:: k.
      Proof with eauto using ok_data_strengthening, ok_kind_strengthening with mcore.
        introv Htk. remember (G1 & x ~ BindVar T2 & G2). gen G2.
        induction Htk; intros; substs...
        { Case "TyFVar". constructor~. binds_cases H0 ; auto. }
        { Case "TyAll". apply_fresh KAll as X...
          apply_ih_bind H1 ; eauto. constructor... }
        { Case "TySem". constructor~.
          apply* Forall_pred_incl. intros p (ty1'&Hwf).
          eexists. apply* ok_pat_strengthening. }
      Qed.

      Lemma ok_data_tvar_strengthening :
        forall G1 G2 x k d,
          ok_data (G1 & x ~ BindTVar k & G2) d ->
          ok_data (G1 & G2) d.
      Proof.
        introv Hd.
        remember (G1 & x ~ BindTVar k & G2) as Gamma.
        induction Hd ; constructor*.
        - substs ; binds_cases H0 ; auto.
        - induction* H1 ; substs ; constructors*.
          binds_cases H3 ; eauto.
      Qed.

      Lemma ok_kind_tvar_strengthening :
        forall G1 G2 x k' k,
          ok_kind (G1 & x ~ BindTVar k' & G2) k ->
          ok_kind (G1 & G2) k.
      Proof.
        introv Hk. remember (G1 & x ~ BindTVar k' & G2) as Gamma.
        destruct* Hk. constructor. substs. apply* ok_data_tvar_strengthening.
      Qed.

      Lemma ok_data_match_strengthening :
        forall G2 G1 M t p m d,
          ok_data (G1 & M ~ BindMatch t p m & G2) d ->
          ok_data (G1 & G2) d.
      Proof.
        introv Hd. remember (G1 & M ~ BindMatch t p m & G2).
        induction Hd ; constructor~.
        - substs ; binds_cases H0 ; auto.
        - induction H1 ; substs ; constructors*.
          binds_cases H3 ; eauto.
      Qed.

      Lemma ok_kind_match_strengthening :
        forall G2 G1 M t p m k,
          ok_kind (G1 & M ~ BindMatch t p m & G2) k ->
          ok_kind (G1 & G2) k.
      Proof.
        introv Hk. remember (G1 & M ~ BindMatch t p m & G2).
        destruct* Hk. constructor. substs. apply* ok_data_match_strengthening.
      Qed.

      Lemma ok_type_match_strengthening :
        forall G2 G1 M t p m T k,
          G1 & M ~ BindMatch t p m & G2 |= T ~:: k ->
          ok_env (G1 & G2) ->
          G1 & G2 |= T ~:: k.
      Proof with eauto using ok_data_match_strengthening, ok_kind_match_strengthening with mcore.
        introv Htk.
        remember (G1 & M ~ BindMatch t p m & G2). gen G2.
        induction Htk; intros; substs...
        { Case "TyFVar". constructor~. binds_cases H0 ; auto. }
        { Case "TyAll". apply_fresh KAll as X...
          apply_ih_bind H1 ; eauto. constructor... }
        { Case "TySem". constructor~.
          apply* Forall_pred_incl. intros p' (ty1'&Hwf).
          eexists. apply* ok_pat_match_strengthening. }
      Qed.

      Lemma ok_data_tname_strengthening :
        forall G2 G1 T d,
          T \notin Tfv_d d ->
          ok_data (G1 & T ~ BindTName & G2) d ->
          ok_data (G1 & G2) d.
      Proof.
        introv Hfv Hd. remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma.
        unfolds Tfv_d. induction Hd ; substs ; constructor ; rew_listx in Hfv ; simpls~.
        - binds_cases H0 ; auto. notin_false.
        - induction* Ks. inverts H1.
          constructors~. binds_cases H8 ; eauto.
      Qed.

      Lemma ok_kind_tname_strengthening :
        forall T G2 G1 k,
          T \notin Tfv_k k ->
          ok_kind (G1 & T ~ BindTName & G2) k ->
          ok_kind (G1 & G2) k.
      Proof with eauto using ok_data_tname_strengthening with mcore.
        introv Hfv Hk.
        remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma.
        induction Hk ; substs...
      Qed.

      Lemma ok_type_tname_strengthening :
        forall T G2 G1 ty k,
          T \notin Tfv_ty ty ->
          G1 & T ~ BindTName & G2 |= ty ~:: k ->
          ok_env (G1 & G2) ->
          G1 & G2 |= ty ~:: k.
      Proof with eauto using ok_data_tname_strengthening, ok_kind_tname_strengthening with mcore.
        introv Hfv Htk Henv.
        remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma. gen G2.
        induction Htk ; intros ; simpls ; substs...
        { Case "TyFVar". constructor~. binds_cases H0 ; auto. }
        { Case "TyAll". rewrite notin_union in Hfv ; destruct Hfv.
          apply_fresh KAll as X...
          apply_ih_bind H1 ; auto. rewrite topen_notin_T ; simpls~. constructors... }
        { Case "TySem". constructor~. apply* Forall_pred_incl.
          intros p (ty1'&Hwf). eexists. apply* ok_pat_tname_strengthening ; auto. }
        { Case "TyDataSub". applys~ KDataSub d1.
          apply* ok_data_tname_strengthening.
          forwards~ Hd1 : IHHtk. forwards Hk : ok_type_ok_kind Hd1.
          inverts Hk. forwards~ Hnin : ok_data_notin_T T H3.
          forwards* (Hfr1&Hfr2) : ok_middle_inv G1 G2.
          apply* data_sub_notin_T. }
      Qed.

      Lemma ok_data_con_strengthening :
        forall K G2 G1 d' ty' T d,
          K \notin Kfv_d d ->
          ok_data (G1 & K ~ BindCon d' ty' T & G2) d ->
          ok_data (G1 & G2) d.
      Proof.
        introv Hfv Hd. remember (G1 & K ~ BindCon d' ty' T & G2) as Gamma eqn:HGamma.
        unfolds Kfv_d. induction Hd ; substs ; constructor ; rew_listx in Hfv ; simpls~.
        - binds_cases H0 ; auto.
        - induction* Ks. inverts H1. rew_listx in Hfv ; simpls~.
          constructors~. binds_cases H8 ; eauto. notin_false.
      Qed.

      Lemma ok_kind_con_strengthening :
        forall K G2 G1 d ty' T k,
          K \notin Kfv_k k ->
          ok_kind (G1 & K ~ BindCon d ty' T & G2) k ->
          ok_kind (G1 & G2) k.
      Proof with eauto using ok_data_con_strengthening with mcore.
        introv Hfv Hk.
        remember (G1 & K ~ BindCon d ty' T & G2) as Gamma eqn:HGamma.
        induction Hk ; substs...
      Qed.

      Lemma ok_type_con_strengthening :
        forall K G2 G1 d ty' T ty k,
          K \notin Kfv_ty ty ->
          G1 & K ~ BindCon d ty' T & G2 |= ty ~:: k ->
          ok_env (G1 & G2) ->
          G1 & G2 |= ty ~:: k.
      Proof with eauto using ok_data_con_strengthening, ok_kind_con_strengthening with mcore.
        introv Hfv Htk Henv.
        remember (G1 & K ~ BindCon d ty' T & G2) as Gamma eqn:HGamma. gen G2.
        induction Htk ; intros ; simpls ; substs...
        { Case "TyFVar". constructor~. binds_cases H0 ; auto. }
        { Case "TyAll". rewrite notin_union in Hfv ; destruct Hfv.
          apply_fresh KAll as X...
          apply_ih_bind H1 ; auto. rewrite topen_notin_K ; simpls~. constructors... }
        { Case "TySem". constructor~. apply* Forall_pred_incl.
          intros p (ty1'&Hwf). eexists. apply* ok_pat_con_strengthening ; auto. }
        { Case "TyDataSub". applys~ KDataSub d1.
          apply* ok_data_con_strengthening.
          forwards~ Hd1 : IHHtk. forwards Hk : ok_type_ok_kind Hd1.
          inverts Hk. forwards~ Hnin : ok_data_notin_K K H3.
          forwards* (Hfr1&Hfr2) : ok_middle_inv G1 G2.
          apply* data_sub_notin_K. }
      Qed.

      Lemma ok_data_tbsubst :
        forall G1 G2 X T d,
          ok_data (G1 & G2) d ->
          ok_data (G1 & map (tbsubst X T) G2) d.
      Proof.
        introv Hd.
        remember (G1 & G2) as Gamma.
        induction Hd ; constructor*.
        - substs ; binds_cases H0 ; auto.
          replaces BindTName with (tbsubst X T BindTName) ; auto.
        - induction* H1 ; substs.
          binds_cases H3 ; constructors*.
          replaces (BindCon d0 ({X => T} ty) T1) with (tbsubst X T (BindCon d0 ty T1)) ; auto.
      Qed.

      Lemma ok_kind_tbsubst :
        forall G1 G2 X T k,
          ok_kind (G1 & G2) k ->
          ok_kind (G1 & map (tbsubst X T) G2) k.
      Proof.
        introv Hk. remember (G1 & G2) as Gamma.
        destruct* Hk. constructor. substs. apply* ok_data_tbsubst.
      Qed.

      Lemma ok_type_tsubst :
        forall G2 G1 X T1 T2 k k',
          G1 & X ~ BindTVar k' & G2 |= T1 ~:: k ->
          G1 |= T2 ~:: k' ->
          ok_env (G1 & map (tbsubst X T2) G2) ->
          G1 & map (tbsubst X T2) G2 |= {X => T2} T1 ~:: k.
      Proof with eauto using ok_data_tbsubst, ok_kind_tbsubst, ok_type_lct,
          ok_data_tvar_strengthening, ok_kind_tvar_strengthening with mcore.
        introv Htk1 Htk2 Henv.
        remember (G1 & X ~ BindTVar k' & G2) as G. gen G2.
        induction Htk1; intros; substs; simpls...
        { Case "TyFVar". solve_var.
          + binds_get H0. lets* [Hok ?] : ok_concat_inv (ok_env_ok _ Henv).
            apply_empty* ok_type_weakening.
          + constructors~. binds_cases H0...
            replaces (BindTVar k) with (tbsubst X T2 (BindTVar k))... }
        { Case "TyAll". apply_fresh KAll... rewrite tsubst_topen_comm...
          replaces (BindTVar k) with (tbsubst X T2 (BindTVar k))...
          apply_ih_map_bind H1 ; auto. constructor... }
        { Case "TySem". constructor~. apply* Forall_pred_incl.
          intros p (ty1'&Hwf). eexists. apply* ok_pat_tsubst. }
      Qed.

      Lemma ok_term_ok_type :
        forall Gamma t ty,
          Gamma |= t ~: ty ->
          Gamma |= ty ~:: KiType.
      Proof with eauto with mcore.
        introv Htype.
        induction* Htype.
        { Case "TmFVar". apply* ok_env_binds_var_inv. }
        { Case "TmLam". constructor~. pick_fresh x. forwards~ Htk : H1 x.
          apply_empty* ok_type_strengthening. }
        { Case "TmApp". inverts~ IHHtype1. }
        { Case "TmTyLam". inverts IHHtype. pick_fresh X. rewrite~ (tsubst_intro X).
          apply_empty* ok_type_tsubst. }
        { Case "TmFix". inverts~ IHHtype. }
        { Case "TmProj1". inverts~ IHHtype. }
        { Case "TmProj2". inverts~ IHHtype. }
        { Case "TmMatch". pick_fresh M. pick_fresh x. forwards~ Htk : H1 M x.
          apply_empty* ok_type_match_strengthening. apply_empty ok_type_strengthening... }
        { Case "TmType". pick_fresh T. apply_empty* (ok_type_tname_strengthening T). }
        { Case "TmConDef". pick_fresh K. apply_empty* (ok_type_con_strengthening K). }
        { Case "TmSem". constructor ; rew_listx*.
          pick_fresh x. forwards~ Htk : H2 x.
          apply_empty* ok_type_strengthening. }
        { Case "TmComp". inverts IHHtype1. inverts IHHtype2. constructor ; rew_listx~. }
        { Case "TmSemApp". inverts~ IHHtype1. }
      Qed.

      Lemma ok_data_bsubst :
        forall G1 G2 x t d,
          ok_data (G1 & G2) d ->
          ok_data (G1 & map (bsubst x t) G2) d.
      Proof.
        introv Hd.
        remember (G1 & G2) as Gamma.
        induction Hd ; constructor*.
        - substs ; binds_cases H0 ; auto.
          replaces BindTName with (bsubst x t BindTName) ; auto.
        - induction* H1 ; substs.
          binds_cases H3 ; constructors*.
          replaces (BindCon d0 ty T0) with (bsubst x t (BindCon d0 ty T0)) ; auto.
      Qed.

      Lemma ok_kind_bsubst :
        forall G1 G2 X T k,
          ok_kind (G1 & G2) k ->
          ok_kind (G1 & map (bsubst X T) G2) k.
      Proof.
        introv Hk. remember (G1 & G2) as Gamma.
        destruct* Hk. constructor. substs. apply* ok_data_bsubst.
      Qed.

      Lemma ok_type_subst :
        forall G2 G1 x t T1 T2 k,
          G1 & x ~ BindVar T2 & G2 |= T1 ~:: k ->
          ok_env (G1 & map (bsubst x t) G2) ->
          G1 & map (bsubst x t) G2 |= T1 ~:: k.
      Proof with eauto using ok_data_bsubst, ok_kind_bsubst,
          ok_data_strengthening, ok_kind_strengthening with mcore.
        introv Htk. remember (G1 & x ~ BindVar T2 & G2) as G. gen G2.
        induction Htk; intros; substs; simpls...
        { Case "TyFVar". constructor~. binds_cases H0 ; auto.
          replaces (BindTVar k) with (bsubst x t (BindTVar k))... }
        { Case "TyAll". apply_fresh KAll...
          replaces (BindTVar k) with (bsubst x t (BindTVar k))...
          apply_ih_map_bind H1 ; auto. constructor... }
        { Case "TySem". constructor~. apply* Forall_pred_incl.
          intros p (ty1'&Hwf). eexists.
          apply ok_pat_bsubst. apply* ok_pat_strengthening. }
      Qed.

      Lemma ok_term_subst :
        forall G2 G1 x t1 t2 T1 T2,
          G1 & x ~ BindVar T2 & G2 |= t1 ~: T1 ->
          is_value t2 ->
          G1 |= t2 ~: T2 ->
          ok_env (G1 & map (bsubst x t2) G2) ->
          G1 & map (bsubst x t2) G2 |= [x => t2]t1 ~: T1.
      Proof with eauto using ok_data_strengthening, ok_kind_strengthening,
          ok_data_bsubst, ok_kind_bsubst, ok_type_subst with mcore.
        introv Htype1 Hval Htype2.
        remember (G1 & x ~ BindVar T2 & G2). gen G2.
        induction Htype1 ; intros ; simpls ; substs...
        { Case "TmFVar". cases_if.
          - binds_get H0... apply_empty ok_term_weakening ; auto.
          - binds_cases H0... constructor ; auto.
            replaces (BindVar ty) with (bsubst x t2 (BindVar ty))... }
        { Case "TmLam". apply_fresh TLam as y...
          replaces (BindVar ty1) with (bsubst x t2 (BindVar ty1))...
          rewrite subst_open_comm... apply_ih_map_bind H1 ; auto.
          constructor... }
        { Case "TmTyLam". apply_fresh* TTyLam as X... rewrite* topen_t_subst_comm.
          replaces (BindTVar k) with (bsubst x t2 (BindTVar k))...
          apply_ih_map_bind H1 ; auto. constructor... }
        { Case "TmCon". constructors... binds_cases H ; auto.
          replaces (BindCon d ty1 (FTName T))
            with (bsubst x t2 (BindCon d ty1 (FTName T)))... }
        { Case "TmMatch". apply_fresh TMatch ; intros...
          - apply ok_pat_bsubst. apply* ok_pat_strengthening.
          - replaces (BindVar ty1') with (bsubst x t2 (BindVar ty1'))...
            replaces (BindMatch ([x => t2]t) p true) with (bsubst x t2 (BindMatch t p true))...
            rewrite subst_open_comm...
            do_rew_2 concat_assoc_map_push (applys H1 M) ; auto. rewrite_all~ concat_assoc.
            constructor~.
            + constructors... apply ok_pat_bsubst. apply* ok_pat_strengthening.
            + apply_ih_map_bind ok_type_subst ; eauto ; try rewrite concat_assoc.
              apply_empty ok_type_weakening. apply* ok_pat_ok_type. constructors...
              constructors... apply ok_pat_bsubst. apply* ok_pat_strengthening.
          - replaces (BindMatch ([x => t2]t) p false) with (bsubst x t2 (BindMatch t p false))...
            apply_ih_map_bind H3 ; auto. constructors...
            apply ok_pat_bsubst. apply* ok_pat_strengthening. }
        { Case "TmNever". constructor... apply* contradictory_subst. }
        { Case "TmType". apply_fresh TType as T... rewrite* Topen_t_subst_comm.
          replaces BindTName with (bsubst x t2 BindTName)...
          apply_ih_map_bind H0 ; auto. constructor... }
        { Case "TmConDef". apply_fresh TConDef as K...
          - replaces (BindTVar (KiData d)) with (bsubst x t2 (BindTVar (KiData d)))...
            apply_ih_map_bind ok_type_subst ; auto. rewrite~ concat_assoc. constructor...
          - binds_cases H1 ; auto.
            replaces BindTName with (bsubst x t2 BindTName)...
          - replaces (BindCon d ty1 (FTName T))
              with (bsubst x t2 (BindCon d ty1 (FTName T)))...
            rewrite* Kopen_t_subst_comm. apply_ih_map_bind H3 ; auto.
            apply_fresh EnvCon as X...
            { replaces (BindTVar (KiData d)) with (bsubst x t2 (BindTVar (KiData d)))...
              apply_ih_map_bind ok_type_subst ; auto. rewrite~ concat_assoc. constructor... }
            { binds_cases H1 ; auto.
              replaces BindTName with (bsubst x t2 BindTName)... } }
        { Case "TmSem". apply_fresh TSem as y...
          - apply ok_pat_bsubst. apply* ok_pat_strengthening.
          - replaces (BindVar ty1') with (bsubst x t2 (BindVar ty1'))...
            rewrite subst_open_comm... apply_ih_map_bind H2 ; auto.
            constructor... applys ok_type_subst... applys* ok_pat_ok_type. }
        { Case "TmSemApp". constructors...
          apply exhaustive_bsubst. apply* exhaustive_strengthening. }
      Qed.

      Lemma ok_type_notin :
        forall Gamma T k X,
          Gamma |= T ~:: k ->
          X # Gamma ->
          X \notin tfv T.
      Proof.
        introv Htk Hfresh.
        induction Htk; simpls*.
        { Case "TyFVar". intros contra.
          rewrite in_singleton in contra. substs.
          apply get_none in Hfresh.
          apply binds_get in H0.
          fequals. }
        { Case "TyAll". pick_fresh Y.
          forwards~ Hnin : topen_notin (H1 Y). }
      Qed.

      Lemma ok_term_notin :
        forall Gamma t T X,
          Gamma |= t ~: T ->
          X # Gamma ->
          X \notin tfv_t t.
      Proof with eauto using ok_type_notin.
        introv Htype Hfresh.
        induction Htype; simpls...
        - pick_fresh x. forwards Hnin : open_notin (H1 x)...
        - pick_fresh Y. forwards~ Hnin : topen_t_notin (H1 Y).
        - pick_fresh M. pick_fresh x. forwards~ Hnin1 : open_notin (H1 M x).
          forwards~ Hnin2 : H3 M.
        - pick_fresh T. forwards~ Hnin : Topen_t_notin (H0 T).
        - pick_fresh K. forwards~ Hnin1 : Kopen_t_notin (H3 K).
          forwards~ Hnin2 : ok_type_notin X (H0 K).
          forwards~ Hnin2' : topen_notin Hnin2.
        - pick_fresh x. forwards~ Hnin1 : open_notin (H2 x).
          forwards~ Hnin2 : ok_type_notin X H.
      Qed.

      Lemma env_tbsubst_fresh :
        forall Gamma X T2,
          ok_env Gamma ->
          X # Gamma ->
          Gamma = map (tbsubst X T2) Gamma.
      Proof.
        introv Henv Hfresh.
        induction Henv ; autorewrite with rew_env_map ; repeat fequals ; simpls~.
        { Case "BindCon". rewrite* tsubst_fresh.
          pick_fresh X'. forwards~ Hnin : ok_type_notin X (H1 X').
          applys~ topen_notin Hnin. }
        { Case "BindVar". rewrite* tsubst_fresh.
          apply* ok_type_notin. }
        { Case "BindMatch". rewrite* tsubst_t_fresh.
          apply* ok_term_notin. }
      Qed.

      Lemma ok_term_tsubst :
        forall G2 G1 t k T1 T2 X,
          G1 & X ~ BindTVar k & G2 |= t ~: T1 ->
          G1 |= T2 ~:: k ->
          ok_env (G1 & map (tbsubst X T2) G2) ->
          G1 & map (tbsubst X T2) G2 |= [{X => T2}]t ~: ({X => T2}T1).
      Proof with eauto using ok_data_tvar_strengthening, ok_kind_tvar_strengthening,
          ok_data_tbsubst, ok_kind_tbsubst, ok_type_tsubst, ok_type_lct with mcore.
        introv hasType Henv.
        remember (G1 & X ~ BindTVar k & G2) as G. gen G2.
        induction hasType; intros; simpls; substs...
        { Case "TmFVar". constructor...
          replaces (BindVar ({X => T2} ty)) with (tbsubst X T2 (BindVar ty))...
          binds_cases H0 ; auto.
          assert (X # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite* (env_tbsubst_fresh G1 X T2). }
        { Case "TmLam". apply_fresh TLam as x...
          replaces (BindVar ({X => T2}ty1)) with (tbsubst X T2 (BindVar ty1))...
          rewrite tsubst_t_open_comm. apply_ih_map_bind H1 ; auto.
          constructor... }
        { Case "TmTyLam". apply_fresh TTyLam...
          replaces (BindTVar k0) with (tbsubst X T2 (BindTVar k0))...
          rewrite tsubst_topen_comm... rewrite topen_t_tsubst_comm...
          apply_ih_map_bind H1 ; auto. constructor... }
        { Case "TmTyApp". rewrite tsubst_topen_distr... }
        { Case "TmCon".
          apply TCon with (d := d) (ty1 := {X => T2}ty1) ; try apply* ok_type_tsubst.
          - replaces (BindCon d ({X => T2} ty1) (FTName T)) with (tbsubst X T2 (BindCon d ty1 (FTName T)))...
            binds_cases H ; auto.
            assert (X # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
            rewrite* (env_tbsubst_fresh G1 X T2).
          - rewrite <- tsubst_topen_distr... }
        { Case "TmMatch". apply_fresh TMatch ; intros...
          - applys* ok_pat_tsubst.
          - replaces (BindVar ({X => T2}ty1')) with (tbsubst X T2 (BindVar ty1'))...
            replaces (BindMatch ([{X => T2}]t) p true) with (tbsubst X T2 (BindMatch t p true))...
            rewrite tsubst_t_open_comm.
            do_rew_2 concat_assoc_map_push (applys H1 M) ; auto. rewrite_all~ concat_assoc.
            constructor~.
            + constructors... applys* ok_pat_tsubst.
            + apply_ih_map_bind ok_type_tsubst ; eauto ; try rewrite concat_assoc.
              apply_empty ok_type_weakening. apply* ok_pat_ok_type. constructors...
              constructors... apply* ok_pat_tsubst.
          - replaces (BindMatch ([{X => T2}]t) p false) with (tbsubst X T2 (BindMatch t p false))...
            apply_ih_map_bind H3 ; auto. constructors... apply* ok_pat_tsubst. }
        { Case "TmNever". constructors... applys contradictory_tsubst... }
        { Case "TmType". apply_fresh TType.
          replaces BindTName with (tbsubst X T2 BindTName)...
          rewrite Topen_t_tsubst_comm... apply_ih_map_bind H0 ; auto.
          constructor... }
        { Case "TmConDef".
          apply_fresh TConDef.
          - apply* ok_data_tbsubst. apply* ok_data_tvar_strengthening.
          - replaces (BindTVar (KiData d)) with (tbsubst X T2 (BindTVar (KiData d)))...
            rewrite tsubst_topen_comm...
            apply_ih_map_bind ok_type_tsubst ; eauto ; try rewrite* concat_assoc. constructor...
          - binds_cases H1 ; auto.
            replaces BindTName with (tbsubst X T2 BindTName) ; auto.
          - replaces (BindCon d ({X => T2} ty1) (FTName T)) with (tbsubst X T2 (BindCon d ty1 (FTName T)))...
            rewrite Kopen_t_tsubst_comm... apply_ih_map_bind H3 ; auto.
            apply_fresh EnvCon...
            + replaces (BindTVar (KiData d)) with (tbsubst X T2 (BindTVar (KiData d)))...
              rewrite tsubst_topen_comm...
              apply_ih_map_bind ok_type_tsubst ; eauto ; try rewrite* concat_assoc. constructor...
            + binds_cases H1 ; auto.
              replaces BindTName with (tbsubst X T2 BindTName) ; auto. }
        { Case "TmSem". apply_fresh TSem as x...
          + applys* ok_pat_tsubst.
          + replaces (BindVar ({X => T2}ty1')) with (tbsubst X T2 (BindVar ty1'))...
            rewrite tsubst_t_open_comm. apply_ih_map_bind H2 ; auto.
            constructor... applys* ok_type_tsubst. apply* ok_pat_ok_type. }
        { Case "TmSemApp". constructors*. apply* exhaustive_tsubst. }
      Qed.

      Lemma ok_data_comm :
        forall G2 G1 x1 x2 b1 b2 d,
          ok_data (G1 & x1 ~ b1 & x2 ~ b2 & G2) d ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          ok_data (G1 & x2 ~ b2 & x1 ~ b1 & G2) d.
      Proof.
        introv Hd Henv. remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma.
        induction Hd ; substs ; constructor~.
        - binds_cases H0 ; auto.
          apply* binds_concat_left_ok. apply* binds_concat_left_ok.
          applys* ok_concat_inv_l G2.
        - induction* Ks. inverts H1.
          constructors~. binds_cases H8 ; eauto.
          apply* binds_concat_left_ok. apply* binds_concat_left_ok.
          applys* ok_concat_inv_l G2.
      Qed.

      Lemma ok_kind_comm :
        forall G2 G1 x1 x2 b1 b2 k,
          ok_kind (G1 & x1 ~ b1 & x2 ~ b2 & G2) k ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          ok_kind (G1 & x2 ~ b2 & x1 ~ b1 & G2) k.
      Proof with eauto using ok_data_comm with mcore.
        introv Hk Henv.
        remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma.
        induction Hk ; substs...
      Qed.

      Lemma ok_type_comm :
        forall G2 G1 x1 x2 b1 b2 ty k,
          G1 & x1 ~ b1 & x2 ~ b2 & G2 |= ty ~:: k ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          G1 & x2 ~ b2 & x1 ~ b1 & G2 |= ty ~:: k.
      Proof with eauto using ok_data_comm, ok_kind_comm with mcore.
        introv Htk Henv.
        remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma. gen G2.
        induction Htk ; intros ; substs...
        { Case "TyFVar". constructor~. binds_cases H0 ; auto.
          apply* binds_concat_left_ok. apply* binds_concat_left_ok.
          applys* ok_concat_inv_l G2. }
        { Case "TyAll". apply_fresh KAll as X...
          apply_ih_bind H1 ; auto. constructors... }
        { Case "TySem". constructor~. apply* Forall_pred_incl.
          intros x (ty1'&Hwf). eexists. apply* ok_pat_comm. }
      Qed.

      Lemma ok_term_comm :
        forall G2 G1 x1 x2 b1 b2 t ty,
          G1 & x1 ~ b1 & x2 ~ b2 & G2 |= t ~: ty ->
          ok_env (G1 & x2 ~ b2 & x1 ~ b1 & G2) ->
          G1 & x2 ~ b2 & x1 ~ b1 & G2 |= t ~: ty.
      Proof with eauto using ok_data_comm, ok_kind_comm, ok_type_comm with mcore.
        introv Htype Henv.
        remember (G1 & x1 ~ b1 & x2 ~ b2 & G2) as Gamma eqn:HGamma. gen G2.
        induction Htype ; intros ; substs...
        { Case "TmFVar". constructor~. binds_cases H0 ; auto.
          apply* binds_concat_left_ok. apply* binds_concat_left_ok.
          applys* ok_concat_inv_l G2. }
        { Case "TmLam". apply_fresh TLam as x...
          apply_ih_bind H1 ; auto. constructor... }
        { Case "TmTyLam". apply_fresh TTyLam as X...
          apply_ih_bind H1 ; auto. constructor... }
        { Case "TmCon". constructors... binds_cases H...
          apply* binds_concat_left_ok. apply* binds_concat_left_ok.
          applys* ok_concat_inv_l G2. }
        { Case "TmMatch". apply_fresh TMatch ; intros...
          + apply* ok_pat_comm.
          + do_rew_2 concat_assoc (applys H1 M) ; auto. easy.
            constructor~. constructors... apply* ok_pat_comm.
            apply_empty~ ok_type_weakening. apply~ ok_type_comm. apply* ok_pat_ok_type.
            constructors... apply* ok_pat_comm.
          + apply_ih_bind H3 ; eauto ; auto. constructors... apply* ok_pat_comm. }
        { Case "TmNever". constructor... apply~ contradictory_comm. }
        { Case "TmType". apply_fresh TType as T...
          apply_ih_bind H0 ; auto. constructor... }
        { Case "TmConDef".
          assert (binds T BindTName (G1 & x2 ~ b2 & x1 ~ b1 & G2)).
          { binds_cases H1...
            apply* binds_concat_left_ok. apply* binds_concat_left_ok.
            applys* ok_concat_inv_l G2. }
          apply_fresh TConDef as X...
          + apply_ih_bind ok_type_comm. eauto. constructor...
          + apply_ih_bind H3 ; auto. apply_fresh EnvCon as X'...
            apply_ih_bind ok_type_comm. eauto. constructor... }
        { Case "TmSem". apply_fresh TSem as x...
          + apply* ok_pat_comm.
          + apply_ih_bind H2 ; auto. constructor... apply~ ok_type_comm. apply* ok_pat_ok_type. }
        { Case "TmSemApp". constructors~. apply~ exhaustive_comm. }
      Qed.

      Lemma env_Tbsubst_fresh :
        forall Gamma X T,
          ok_env Gamma ->
          X # Gamma ->
          Gamma = map (Tbsubst X T) Gamma.
      Proof.
        introv Henv Hfresh.
        induction Henv ; autorewrite with rew_env_map ; repeat fequals ; simpls~.
        { Case "BindCon". fequals.
          - rewrite~ Tsubst_d_fresh. forwards~ Hnin : ok_data_notin_T X H0.
          - rewrite~ Tsubst_ty_fresh. pick_fresh X'.
            forwards~ Hnin : ok_type_notin_T X (H1 X').
            rewrite topen_notin_T in Hnin ; simpls~.
          - solve_var. forwards* Hin : get_some_inv T0.
            assert (Hnin: T0 # Gamma) by auto. contradiction. }
        { Case "BindTVar". fequals.
          rewrite~ Tsubst_k_fresh. apply* ok_kind_notin_T. }
        { Case "BindVar". fequals.
          rewrite~ Tsubst_ty_fresh. apply* ok_type_notin_T. }
        { Case "BindMatch". fequals.
          rewrite~ Tsubst_t_fresh. apply* ok_term_notin_T. }
      Qed.

      Lemma assoc_Tsubst :
        forall T T' S Ks d,
          mem (FTName S, Ks) d ->
          mem (Tsubst T (FTName T') (FTName S), Ks) (Tsubst_d T (FTName T') d).
      Proof.
        introv Hassoc. unfolds Tsubst_d.
        induction Hassoc ; rew_listx~.
      Qed.

      Lemma assoc_Tsubst_inv :
        forall Gamma T T' S Ks d,
          ok_data Gamma d ->
          T' # Gamma ->
          T' <> S ->
          mem (Tsubst T (FTName T') (FTName S), Ks) (Tsubst_d T (FTName T') d) ->
          mem (FTName S, Ks) d.
      Proof.
        introv Hd Hfresh Hneq Hassoc. unfolds Tsubst_d.
        induction Hd ; inverts Hassoc ; rew_listx~.
        left. fequals. rewrite~ (Tsubst_inj S T0 T T').
        intro Heq ; substs. forwards Hin : get_some_inv T0 ; eauto.
      Qed.

      Lemma ok_data_Tsubst :
        forall G2 G1 T T' d,
          ok_data (G1 & T ~ BindTName & G2) d ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_env (G1 & T ~ BindTName & G2) ->
          ok_data (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2)
                  (Tsubst_d T (FTName T') d).
      Proof with eauto with mcore.
        introv Hd Hfresh Henv. assert (Henv' : ok_env G1)
          by (applys ok_env_concat ; applys* ok_env_concat).
        remember (G1 & T ~ BindTName & G2). unfolds Tsubst_d.
        induction Hd; substs; rew_listx*.
        asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
        rewrite Heq. constructor~.
        - rewrite <- Heq. folds (Tsubst_d T (FTName T') d). introv contra.
          apply (assoc_Tsubst_inv (G1 & T ~ BindTName & G2)) in contra ; jauto.
          intro ; substs. forwards~ Hin : get_some_inv H0.
        - solve_var ; inverts~ Heq. binds_cases H0 ; auto.
          apply~ binds_concat_left. apply binds_concat_left_ok...
          replaces BindTName with (Tbsubst T (FTName T') BindTName)...
        - remember (FTName T0). remember (G1 & T ~ BindTName & G2).
          induction H1 ; substs.
          + constructor.
          + apply CCons with (d := Tsubst_d T (FTName T') d0)
                             (ty := Tsubst_ty T (FTName T') ty) ; auto.
            replaces (BindCon (Tsubst_d T (FTName T') d0) (Tsubst_ty T (FTName T') ty) (FTName S))
              with (Tbsubst T (FTName T') (BindCon d0 ty (FTName T0))). rewrite~ <- Heq.
            binds_cases H3 ; auto.
            apply~ binds_concat_left. apply binds_concat_left_ok...
            assert (T # G1). applys ok_push_inv...
            rewrite~ (env_Tbsubst_fresh G1 T (FTName T'))...
      Qed.

      Lemma ok_kind_Tsubst :
        forall G2 G1 T T' k,
          ok_kind (G1 & T ~ BindTName & G2) k ->
          ok_env  (G1 & T ~ BindTName & G2) ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_kind (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2)
                  (Tsubst_k T (FTName T') k).
      Proof.
        introv Hk. remember (G1 & T ~ BindTName & G2) as G.
        induction Hk; intros; substs; constructor.
        apply~ ok_data_Tsubst.
      Qed.

      Lemma data_sub_Tsubst :
        forall T U d1 d2,
          data_sub d2 d1 ->
          data_sub (Tsubst_d T U d2) (Tsubst_d T U d1).
      Proof.
        introv Hsub Hmem. unfolds data_sub. unfolds Tsubst_d.
        induction d2 ; rew_listx* in Hmem. destruct a.
        destruct~ Hmem as [Heq | Hmem'].
        inverts Heq. forwards~ (Ks&Hmem&?) : Hsub.
        exists Ks. split~. apply* mem_map'.
      Qed.

      Lemma ok_type_Tsubst :
        forall G2 G1 T T' ty k,
          G1 & T ~ BindTName & G2 |= ty ~:: k ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_env  (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2) ->
          G1 & T' ~ BindTName &
            map (Tbsubst T (FTName T')) G2 |=
                Tsubst_ty T (FTName T') ty ~:: Tsubst_k T (FTName T') k.
      Proof with eauto using ok_kind_Tsubst, ok_data_Tsubst with mcore.
        introv Htk Hfresh Henv. assert (Henv' : ok_env G1)
          by (applys ok_env_concat ; applys* ok_env_concat).
        remember (G1 & T ~ BindTName & G2) as G. gen G2.
        induction Htk; intros; substs; simpls...
        { Case "TyFVar". constructor...
          replaces (BindTVar (Tsubst_k T (FTName T') k))
            with (Tbsubst T (FTName T') (BindTVar k))... binds_cases H0 ; auto.
          apply~ binds_concat_left. apply* binds_concat_left_ok.
          assert (T # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite~ (env_Tbsubst_fresh G1 T (FTName T')). }
        { Case "TyAll". apply_fresh KAll as X...
          replaces (BindTVar (Tsubst_k T (FTName T') k))
            with (Tbsubst T (FTName T') (BindTVar k))...
          rewrite <- Tsubst_ty_topen_comm. apply_ih_map_bind H1 ; auto.
          constructor... }
        { Case "TyCon".
          asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
          simpls. rewrite Heq. apply KCon with (d := Tsubst_d T (FTName T') d) (Ks := Ks)...
          rewrite <- Heq. applys~ assoc_Tsubst. }
        { Case "TySem". constructor~. apply* Forall_pred_incl.
          intros p (ty1'&Hwf). eexists. apply ok_pat_Tsubst ; eauto. apply* ok_type_ok_env. }
        { Case "TyDataSub". applys KDataSub (Tsubst_d T (FTName T') d1)...
          apply~ data_sub_Tsubst. }
      Qed.

      Lemma ok_term_Tsubst :
        forall G2 G1 T T' t ty,
          G1 & T ~ BindTName & G2 |= t ~: ty ->
          T' # G1 & T ~ BindTName & G2 ->
          ok_env (G1 & T' ~ BindTName & map (Tbsubst T (FTName T')) G2) ->
          G1 & T' ~ BindTName &
            map (Tbsubst T (FTName T')) G2 |=
                Tsubst_t T (FTName T') t ~: Tsubst_ty T (FTName T') ty.
      Proof with eauto using ok_type_Tsubst, ok_kind_Tsubst, ok_data_Tsubst with mcore.
        introv Htype. assert (Henv : ok_env G1)
          by (applys ok_env_concat ; applys* ok_env_concat).
        remember (G1 & T ~ BindTName & G2) as Gamma eqn:HGamma. gen G2.
        induction Htype ; intros ; substs...
        { Case "TmFVar". constructor...
          replaces (BindVar (Tsubst_ty T (FTName T') ty))
            with (Tbsubst T (FTName T') (BindVar ty))... binds_cases H0 ; auto.
          apply~ binds_concat_left. apply* binds_concat_left_ok.
          assert (T # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite~ (env_Tbsubst_fresh G1 T (FTName T')). }
        { Case "TmLam". apply_fresh TLam as x.
          + replaces KiType with (Tsubst_k T (FTName T') KiType)...
          + rewrite <- Tsubst_t_open_comm. folds (Tsubst_ty T (FTName T') ty1).
            replaces (BindVar (Tsubst_ty T (FTName T') ty1))
              with (Tbsubst T (FTName T') (BindVar ty1))...
            apply_ih_map_bind H1 ; auto. constructor...
            replaces KiType with (Tsubst_k T (FTName T') KiType)... }
        { Case "TmTyLam". apply_fresh TTyLam as X...
          rewrite <- Tsubst_t_topen_comm. rewrite <- Tsubst_ty_topen_comm.
          replaces (BindTVar (Tsubst_k T (FTName T') k))
            with (Tbsubst T (FTName T') (BindTVar k))...
          apply_ih_map_bind H1 ; auto. constructor... }
        { Case "TmTyApp". rewrite Tsubst_ty_topen_distr... }
        { Case "TmCon".
          asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
          simpls. rewrite Heq.
          apply TCon with (d := Tsubst_d T (FTName T') d) (ty1 := Tsubst_ty T (FTName T') ty1).
          - replaces (BindCon (Tsubst_d T (FTName T') d) (Tsubst_ty T (FTName T') ty1) (FTName S))
              with (Tbsubst T (FTName T') (BindCon d ty1 (FTName T0))). rewrite~ <- Heq.
            binds_cases H ; auto.
            apply~ binds_concat_left. apply* binds_concat_left_ok.
            assert (T # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
            rewrite~ (env_Tbsubst_fresh G1 T (FTName T')).
          - replaces (KiData (Tsubst_d T (FTName T') d)) with (Tsubst_k T (FTName T') (KiData d))...
          - replaces (KiData [(FTName S, FCon K :: [])])
              with (Tsubst_k T (FTName T') (KiData [(FTName T0, FCon K :: [])]))... rewrite~ <- Heq.
          - rewrite <- Tsubst_ty_topen_distr... }
        { Case "TmMatch". apply_fresh TMatch ; intros...
          - apply ok_pat_Tsubst...
          - rewrite <- Tsubst_t_open_comm. folds (Tsubst_t T (FTName T') t).
            replaces (BindMatch (Tsubst_t T (FTName T') t) p true)
              with (Tbsubst T (FTName T') (BindMatch t p true))...
            replaces (BindVar (Tsubst_ty T (FTName T') ty1'))
              with (Tbsubst T (FTName T') (BindVar ty1'))...
            do_rew_2 concat_assoc_map_push (applys H1 M x) ; auto. rewrite_all~ concat_assoc.
            constructor~.
            + constructors... applys* ok_pat_Tsubst.
            + replaces KiType with (Tsubst_k T (FTName T') KiType)...
              apply_ih_map_bind ok_type_Tsubst ; eauto ; try rewrite concat_assoc.
              apply_empty ok_type_weakening. apply* ok_pat_ok_type. constructors...
              constructors... apply* ok_pat_Tsubst.
          - folds (Tsubst_t T (FTName T') t).
            replaces (BindMatch (Tsubst_t T (FTName T') t) p false)
              with (Tbsubst T (FTName T') (BindMatch t p false))...
            apply_ih_map_bind H3 ; auto. constructors... apply* ok_pat_Tsubst. }
        { Case "TmNever". constructor.
          - replaces KiType with (Tsubst_k T (FTName T') KiType)...
          - apply contradictory_Tsubst... }
        { Case "TmType". apply_fresh TType as T0.
          replaces BindTName with (Tbsubst T (FTName T') BindTName)...
          rewrite~ Tsubst_t_Topen_comm. apply_ih_map_bind H0 ; auto. constructor... }
        { Case "TmConDef".
          asserts (S, Heq): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
          simpls. rewrite Heq. apply_fresh TConDef as X...
          - replaces KiType with (Tsubst_k T (FTName T') KiType)...
            replaces (BindTVar (KiData (Tsubst_d T (FTName T') d)))
              with (Tbsubst T (FTName T') (BindTVar (KiData d)))...
            rewrite <- Tsubst_ty_topen_comm.
            apply_ih_map_bind ok_type_Tsubst ; eauto ; try rewrite* concat_assoc.
            constructor...
          - solve_var ; inverts~ Heq.
            binds_cases H1 ; auto.
            apply~ binds_concat_left. apply binds_concat_left_ok...
            replaces BindTName with (Tbsubst T (FTName T') BindTName)...
          - replaces (BindCon (Tsubst_d T (FTName T') d) (Tsubst_ty T (FTName T') ty1) (FTName S))
              with (Tbsubst T (FTName T') (BindCon d ty1 (FTName T0))). rewrite~ <- Heq.
            rewrite Tsubst_t_Kopen_comm. apply_ih_map_bind H3 ; auto.
            asserts (S0, Heq'): (lcT (Tsubst T (FTName T') (FTName T0))). solve_var.
            simpls. rewrite Heq'. apply_fresh EnvCon ; intros...
            + replaces KiType with (Tsubst_k T (FTName T') KiType)...
              replaces (BindTVar (KiData (Tsubst_d T (FTName T') d)))
                with (Tbsubst T (FTName T') (BindTVar (KiData d)))...
              rewrite <- Tsubst_ty_topen_comm.
              apply_ih_map_bind ok_type_Tsubst ; eauto ; try rewrite* concat_assoc.
              constructor...
            + solve_var ; inverts~ Heq'.
              binds_cases H1 ; auto.
              apply~ binds_concat_left. apply binds_concat_left_ok...
              replaces BindTName with (Tbsubst T (FTName T') BindTName)... }
        { Case "TmSem". apply_fresh TSem as x.
          + replaces KiType with (Tsubst_k T (FTName T') KiType)...
          + apply ok_pat_Tsubst...
          + rewrite <- Tsubst_t_open_comm.
            replaces (BindVar (Tsubst_ty T (FTName T') ty1'))
              with (Tbsubst T (FTName T') (BindVar ty1'))...
            apply_ih_map_bind H2 ; auto. constructor...
            replaces KiType with (Tsubst_k T (FTName T') KiType)...
            apply~ ok_type_Tsubst. applys ok_pat_ok_type H0. apply* ok_type_ok_env. }
        { Case "TmSemApp". constructors*. apply* exhaustive_Tsubst. }
      Qed.

      Lemma ok_term_Topen_change :
        forall T T' Gamma t ty,
          T \notin Tfv_t t \u Tfv_ty ty ->
          T' # Gamma & T ~ BindTName ->
          Gamma & T ~ BindTName |= Topen_t 0 (FTName T) t ~: ty ->
          Gamma & T' ~ BindTName |= Topen_t 0 (FTName T') t ~: ty.
      Proof.
        introv Hnin Hfresh Htype.
        rewrite~ (Tsubst_t_intro T (FTName T')).
        rewrite~ <- (Tsubst_ty_fresh T (FTName T')).
        apply_empty~ ok_term_Tsubst.
        constructor~. applys* ok_env_concat.
      Qed.


      Lemma env_Kbsubst_fresh :
        forall Gamma X K,
          ok_env Gamma ->
          X # Gamma ->
          Gamma = map (Kbsubst X K) Gamma.
      Proof.
        introv Henv Hfresh.
        induction Henv ; autorewrite with rew_env_map ; repeat fequals ; simpls~.
        { Case "BindCon". fequals.
          - rewrite~ Ksubst_d_fresh. forwards~ Hnin : ok_data_notin_K X H0.
          - rewrite~ Ksubst_ty_fresh. pick_fresh X'.
            forwards~ Hnin : ok_type_notin_K X (H1 X').
            rewrite topen_notin_K in Hnin ; simpls~. }
        { Case "BindTVar". fequals.
          rewrite~ Ksubst_k_fresh. apply* ok_kind_notin_K. }
        { Case "BindVar". fequals.
          rewrite~ Ksubst_ty_fresh. apply* ok_type_notin_K. }
        { Case "BindMatch". fequals.
          - rewrite~ Ksubst_t_fresh. apply* ok_term_notin_K.
          - rewrite~ Ksubst_p_fresh. apply* ok_pat_notin_K. }
      Qed.

      Lemma assoc_Ksubst :
        forall K K' S Ks d,
          mem (FTName S, Ks) d ->
          mem (FTName S, LibList.map (Ksubst K (FCon K')) Ks) (Ksubst_d K (FCon K') d).
      Proof.
        introv Hassoc. unfolds Ksubst_d.
        induction Hassoc ; rew_listx~.
      Qed.

      Lemma assoc_Ksubst_inv :
        forall K K' S Ks d,
          mem (FTName S, Ks) (Ksubst_d K (FCon K') d) ->
          exists Ks', LibList.mem (FTName S, Ks') d.
      Proof.
        introv Hassoc. unfolds Ksubst_d.
        induction d ; inverts Hassoc ; destruct a ; rew_listx in *.
        - inverts H0. exists~.
        - inverts H. destruct~ IHd as (Ks'&?). exists~ Ks'.
      Qed.

      Lemma mem_Ksubst_inv :
        forall Gamma K K' S Ks T,
          ok_cons Gamma Ks T ->
          K' # Gamma ->
          K' <> S ->
          mem (Ksubst K (FCon K') (FCon S)) (LibList.map (Ksubst K (FCon K')) Ks) ->
          mem (FCon S) Ks.
      Proof.
        introv HKs Hfresh Hneq Hmem.
        induction HKs ; inverts Hmem ; rew_listx~ in *.
        left. fequals.
        rewrite~ (Ksubst_inj S K0 K K'). intro Heq ; substs.
        forwards Hin : get_some_inv H0 ; eauto.
      Qed.

      Lemma ok_data_Ksubst :
        forall G2 G1 K K' d' ty' T d,
          ok_data (G1 & K ~ BindCon d' ty' T & G2) d ->
          K' # G1 & K ~ BindCon d' ty' T & G2 ->
          ok_env (G1 & K ~ BindCon d' ty' T & G2) ->
          ok_data (G1 & K' ~ BindCon d' ty' T & map (Kbsubst K (FCon K')) G2)
                  (Ksubst_d K (FCon K') d).
      Proof with eauto with mcore.
        introv Hd Hfresh Henv. assert (Henv' : ok_env G1)
          by (applys ok_env_concat ; applys* ok_env_concat).
        remember (G1 & K ~ BindCon d' ty' T & G2). unfolds Ksubst_d.
        induction Hd; substs; rew_listx*. constructor~.
        - introv contra. forwards* (Ks'&Hassoc): assoc_Ksubst_inv.
        - binds_cases H0 ; auto.
          apply~ binds_concat_left. apply binds_concat_left_ok...
          replaces BindTName with (Kbsubst K (FCon K') BindTName)...
        - remember (G1 & K ~ BindCon d' ty' T & G2).
          induction H1 ; substs.
          + constructor.
          + asserts (S, Heq): (lcK (Ksubst K (FCon K') (FCon K0))). solve_var.
            rew_listx. rewrite Heq.
            apply CCons with (d := Ksubst_d K (FCon K') d0)
                             (ty := Ksubst_ty K (FCon K') ty) ; auto.
            * rewrite <- Heq. intro contra.
              apply H2. applys* mem_Ksubst_inv contra. intro ; subst.
              forwards~ ?: get_some_inv H3.
            * assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
              solve_var ; inverts Heq.
              ** forwards* Heqbind : binds_middle_eq_inv H3. inverts Heqbind.
                 forwards (?&?&?&Hd'&Htk&?): ok_env_con_inv G1 K0 d' ty' T. applys~ ok_env_concat G2.
                 pick_fresh X. forwards~ Hnin: ok_type_notin_K K0 (Htk X).
                 rewrite topen_notin_K in Hnin ; simpls~. forwards~ Hnin': ok_data_notin_K K0 Hd'.
                 rewrite~ Ksubst_d_fresh. rewrite~ Ksubst_ty_fresh.
              ** replaces (BindCon (Ksubst_d K (FCon K') d0) (Ksubst_ty K (FCon K') ty) T1)
                   with (Kbsubst K (FCon K') (BindCon d0 ty T1))...
                 binds_cases H3 ; auto.
                 apply~ binds_concat_left. apply binds_concat_left_ok...
                 rewrite~ (env_Kbsubst_fresh G1 K (FCon K'))...
      Qed.

      Lemma ok_kind_Ksubst :
        forall G2 G1 K K' d ty' T k,
          ok_kind (G1 & K ~ BindCon d ty' T & G2) k ->
          ok_env  (G1 & K ~ BindCon d ty' T & G2) ->
          K' # G1 & K ~ BindCon d ty' T & G2 ->
          ok_kind (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2)
                  (Ksubst_k K (FCon K') k).
      Proof.
        introv Hk. remember (G1 & K ~ BindCon d ty' T & G2) as G.
        induction Hk; intros; substs; constructor.
        apply~ ok_data_Ksubst.
      Qed.

      Lemma data_sub_Ksubst :
        forall K U d1 d2,
          data_sub d2 d1 ->
          data_sub (Ksubst_d K U d2) (Ksubst_d K U d1).
      Proof.
        introv Hsub Hmem. unfolds data_sub. unfolds Ksubst_d.
        induction d2 ; rew_listx* in Hmem. destruct a.
        destruct~ Hmem as [Heq | Hmem'].
        inverts Heq. forwards~ (Ks&Hmem&HsubK) : Hsub.
        exists (LibList.map (Ksubst K U) Ks). split.
        - apply* mem_map'.
        - introv HmemK. clears IHd2 Hsub Hmem.
          induction l ; rew_listx* in HmemK.
          destruct~ HmemK as [Heq | HmemK'].
          inverts Heq. apply~ mem_map.
      Qed.

      Lemma ok_type_Ksubst :
        forall G2 G1 K K' d ty' T ty k,
          G1 & K ~ BindCon d ty' T & G2 |= ty ~:: k ->
          ok_env (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2) ->
          K' # G1 & K ~ BindCon d ty' T & G2 ->
          G1 & K' ~ BindCon d ty' T &
            map (Kbsubst K (FCon K')) G2 |=
                Ksubst_ty K (FCon K') ty ~:: Ksubst_k K (FCon K') k.
      Proof with eauto using ok_kind_Ksubst, ok_data_Ksubst with mcore.
        introv Htk Hfresh Henv. assert (Henv' : ok_env G1)
          by (applys ok_env_concat ; applys* ok_env_concat).
        remember (G1 & K ~ BindCon d ty' T & G2). gen G2.
        induction Htk; intros; substs; simpls...
        { Case "TyFVar". constructor...
          replaces (BindTVar (Ksubst_k K (FCon K') k))
            with (Kbsubst K (FCon K') (BindTVar k))... binds_cases H0 ; auto.
          apply~ binds_concat_left. apply* binds_concat_left_ok.
          assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite~ (env_Kbsubst_fresh G1 K (FCon K')). }
        { Case "TyAll". apply_fresh KAll as X...
          replaces (BindTVar (Ksubst_k K (FCon K') k))
            with (Kbsubst K (FCon K') (BindTVar k))...
          rewrite <- Ksubst_ty_topen_comm. apply_ih_map_bind H1 ; auto.
          constructor... }
        { Case "TyCon".
          apply KCon with (d := Ksubst_d K (FCon K') d0) (Ks := LibList.map (Ksubst K (FCon K')) Ks)...
          apply~ assoc_Ksubst. }
        { Case "TySem". constructor~. rewrite~ Forall_map_eq.
          apply* Forall_pred_incl. intros p (ty1'&Hwf). eexists.
          apply ok_pat_Ksubst ; eauto. apply* ok_type_ok_env. }
        { Case "TyDataSub". applys KDataSub (Ksubst_d K (FCon K') d1)...
          apply~ data_sub_Ksubst. }
      Qed.

      Lemma ok_term_Ksubst :
        forall G2 G1 K K' d ty' T t ty,
          G1 & K ~ BindCon d ty' T & G2 |= t ~: ty ->
          K' # G1 & K ~ BindCon d ty' T & G2 ->
          ok_env (G1 & K' ~ BindCon d ty' T & map (Kbsubst K (FCon K')) G2) ->
          G1 & K' ~ BindCon d ty' T &
            map (Kbsubst K (FCon K')) G2 |=
                Ksubst_t K (FCon K') t ~: Ksubst_ty K (FCon K') ty.
      Proof with eauto using ok_type_Ksubst, ok_kind_Ksubst, ok_data_Ksubst with mcore.
        introv Htype. assert (Henv : ok_env G1)
          by (applys ok_env_concat ; applys* ok_env_concat).
        remember (G1 & K ~ BindCon d ty' T & G2). gen G2.
        induction Htype ; intros ; substs...
        { Case "TmFVar". constructor...
          replaces (BindVar (Ksubst_ty K (FCon K') ty))
            with (Kbsubst K (FCon K') (BindVar ty))... binds_cases H0 ; auto.
          apply~ binds_concat_left. apply* binds_concat_left_ok.
          assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
          rewrite~ (env_Kbsubst_fresh G1 K (FCon K')). }
        { Case "TmLam". apply_fresh TLam as x.
          + replaces KiType with (Ksubst_k K (FCon K') KiType)...
          + rewrite <- Ksubst_t_open_comm. folds (Ksubst_ty K (FCon K') ty1).
            replaces (BindVar (Ksubst_ty K (FCon K') ty1))
              with (Kbsubst K (FCon K') (BindVar ty1))...
            apply_ih_map_bind H1 ; auto. constructor...
            replaces KiType with (Ksubst_k K (FCon K') KiType)... }
        { Case "TmTyLam". apply_fresh TTyLam as X...
          rewrite <- Ksubst_t_topen_comm. rewrite <- Ksubst_ty_topen_comm.
          replaces (BindTVar (Ksubst_k K (FCon K') k))
            with (Kbsubst K (FCon K') (BindTVar k))...
          apply_ih_map_bind H1 ; auto. constructor... }
        { Case "TmTyApp". rewrite Ksubst_ty_topen_distr... }
        { Case "TmCon".
          asserts (S, Heq): (lcK (Ksubst K (FCon K') (FCon K0))). solve_var.
          simpls. rewrite Heq.
          apply TCon with (d := Ksubst_d K (FCon K') d0) (ty1 := Ksubst_ty K (FCon K') ty1).
          - assert (K # G1) by (applys ok_push_inv ; applys* ok_concat_inv_l G2).
            solve_var ; inverts Heq.
            + forwards* Heqbind : binds_middle_eq_inv H. inverts Heqbind.
              forwards (?&?&?&Hd&Htk&?): ok_env_con_inv G1 S d ty'. apply* ok_env_concat.
              pick_fresh X. forwards~ Hnin: ok_type_notin_K K0 (Htk X).
              rewrite topen_notin_K in Hnin ; simpls~. forwards~ Hnin': ok_data_notin_K K0 Hd.
              rewrite~ Ksubst_d_fresh. rewrite~ Ksubst_ty_fresh.
            + replaces (BindCon (Ksubst_d K (FCon K') d0) (Ksubst_ty K (FCon K') ty1) (FTName T0))
                with (Kbsubst K (FCon K') (BindCon d0 ty1 (FTName T0)))...
              binds_cases H ; auto.
              apply~ binds_concat_left. apply* binds_concat_left_ok.
              rewrite~ (env_Kbsubst_fresh G1 K (FCon K')).
          - replaces (KiData (Ksubst_d K (FCon K') d0)) with (Ksubst_k K (FCon K') (KiData d0))...
          - replaces (KiData [(FTName T0, FCon S :: [])])
              with (Ksubst_k K (FCon K') (KiData [(FTName T0, FCon K0 :: [])]))... rewrite~ <- Heq.
          - rewrite <- Ksubst_ty_topen_distr... }
        { Case "TmMatch". apply_fresh TMatch ; intros...
          - apply ok_pat_Ksubst...
          - rewrite <- Ksubst_t_open_comm. folds (Ksubst_t K (FCon K') t).
            replaces (BindMatch (Ksubst_t K (FCon K') t) (Ksubst_p K (FCon K') p) true)
              with (Kbsubst K (FCon K') (BindMatch t p true))...
            replaces (BindVar (Ksubst_ty K (FCon K') ty1'))
              with (Kbsubst K (FCon K') (BindVar ty1'))...
            do_rew_2 concat_assoc_map_push (applys H1 M x) ; auto. rewrite_all~ concat_assoc.
            constructor~.
            + constructors... applys* ok_pat_Ksubst.
            + replaces KiType with (Ksubst_k K (FCon K') KiType)...
              apply_ih_map_bind ok_type_Ksubst ; eauto ; try rewrite concat_assoc.
              apply_empty ok_type_weakening. apply* ok_pat_ok_type. constructors...
              constructors... apply* ok_pat_Ksubst.
          - folds (Ksubst_t K (FCon K') t).
            replaces (BindMatch (Ksubst_t K (FCon K') t) (Ksubst_p K (FCon K') p) false)
              with (Kbsubst K (FCon K') (BindMatch t p false))...
            apply_ih_map_bind H3 ; auto. constructors... apply* ok_pat_Ksubst. }
        { Case "TmNever". constructor~.
          - replaces KiType with (Ksubst_k K (FCon K') KiType)...
          - apply contradictory_Ksubst... }
        { Case "TmType". apply_fresh TType as T0.
          replaces BindTName with (Kbsubst K (FCon K') BindTName)...
          rewrite~ Ksubst_t_Topen_comm. apply_ih_map_bind H0 ; auto. constructor... }
        { Case "TmConDef". apply_fresh TConDef as X...
          - replaces KiType with (Ksubst_k K (FCon K') KiType)...
            replaces (BindTVar (KiData (Ksubst_d K (FCon K') d0)))
              with (Kbsubst K (FCon K') (BindTVar (KiData d0)))...
            rewrite <- Ksubst_ty_topen_comm.
            apply_ih_map_bind ok_type_Ksubst ; eauto ; try rewrite* concat_assoc.
            constructor...
          - binds_cases H1 ; auto.
            apply~ binds_concat_left. apply binds_concat_left_ok...
            replaces BindTName with (Kbsubst K (FCon K') BindTName)...
          - replaces (BindCon (Ksubst_d K (FCon K') d0) (Ksubst_ty K (FCon K') ty1) (FTName T0))
              with (Kbsubst K (FCon K') (BindCon d0 ty1 (FTName T0)))...
            rewrite~ Ksubst_t_Kopen_comm. apply_ih_map_bind H3 ; auto.
            apply_fresh EnvCon as K...
            + replaces KiType with (Ksubst_k K (FCon K') KiType)...
              replaces (BindTVar (KiData (Ksubst_d K (FCon K') d0)))
                with (Kbsubst K (FCon K') (BindTVar (KiData d0)))...
              rewrite <- Ksubst_ty_topen_comm.
              apply_ih_map_bind ok_type_Ksubst ; eauto ; try rewrite* concat_assoc.
              constructor...
            + binds_cases H1 ; auto.
              apply~ binds_concat_left. apply binds_concat_left_ok...
              replaces BindTName with (Kbsubst K (FCon K') BindTName)... }
        { Case "TmSem". apply_fresh TSem as x.
          + replaces KiType with (Ksubst_k K (FCon K') KiType)...
          + apply ok_pat_Ksubst...
          + rewrite <- Ksubst_t_open_comm.
            replaces (BindVar (Ksubst_ty K (FCon K') ty1'))
              with (Kbsubst K (FCon K') (BindVar ty1'))...
            apply_ih_map_bind H2 ; auto. constructor~.
            replaces KiType with (Ksubst_k K (FCon K') KiType)...
            applys~ ok_type_Ksubst. apply* ok_pat_ok_type. }
        { Case "TmComp". simpls. rew_listx.
          constructor... forwards* Hcomp: compatible_Ksubst __ K'.
          - forwards Htk1 : ok_term_ok_type Htype1. forwards Htk2 : ok_term_ok_type Htype2.
            forwards~ Hnin1 : ok_type_notin_K K' Htk1. forwards~ Hnin2 : ok_type_notin_K K' Htk2.
            simpls. rew_listx*. simpls~.
          - rew_listx* in Hcomp. }
        { Case "TmSemApp". constructors*. apply* exhaustive_Ksubst. }
      Qed.

      Lemma ok_term_Kopen_change :
        forall K K' d ty' T Gamma t ty,
          K \notin Kfv_t t \u Kfv_ty ty ->
          K' # Gamma & K ~ BindCon d ty' T ->
          Gamma & K ~ BindCon d ty' T |= Kopen_t 0 (FCon K) t ~: ty ->
          Gamma & K' ~ BindCon d ty' T |= Kopen_t 0 (FCon K') t ~: ty.
      Proof.
        introv Hnin Hfresh Htype.
        rewrite~ (Ksubst_t_intro K (FCon K')).
        rewrite~ <- (Ksubst_ty_fresh K (FCon K')).
        apply_empty~ ok_term_Ksubst.
        forwards Henv : ok_term_ok_env Htype.
        forwards (?&?&?&?&?&?) : ok_env_con_inv Henv. substs.
        apply_fresh* EnvCon as K. applys* ok_env_concat.
      Qed.

    End TypingProps2.
  End TypingProps1.
End TypingProps.
