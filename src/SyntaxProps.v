From TLC Require Import LibList LibLN.
From MCore Require Import Syntax Tactics.

(****************************************)
(** PROPERTIES OF OPERATIONS ON SYNTAX **)
(****************************************)

Module SyntaxProps (P : PAT).
  Module S := Syntax P.
  Export S.

  Module Type PATPROPS.
    Parameter Kopen_p_lcp :
      forall k T p,
        lcp p ->
        Kopen_p k T p = p.

    Parameter Kopen_p_neq :
      forall i j K K' p,
        i <> j ->
        Kopen_p i K (Kopen_p j K' p) = Kopen_p j K' p ->
        Kopen_p i K p = p.

    Parameter Kopen_p_inj :
      forall i X p1 p2,
        X \notin Kfv_p p1 \u Kfv_p p2 ->
        Kopen_p i (FCon X) p1 = Kopen_p i (FCon X) p2 ->
        p1 = p2.

    Parameter Kclose_p_fresh :
      forall K i p,
        K \notin Kfv_p p ->
        Kclose_p K i p = p.

    Parameter Kopen_p_Kopen_comm :
      forall i j K K' p,
        i <> j ->
        Kopen_p i (FCon K) (Kopen_p j (FCon K') p) =
          Kopen_p j (FCon K') (Kopen_p i (FCon K) p).

    Parameter Kopen_p_Kclose_comm :
      forall i j K K' p,
        i <> j ->
        K <> K' ->
        Kopen_p i (FCon K) (Kclose_p K' j p) =
          Kclose_p K' j (Kopen_p i (FCon K) p).

    Parameter Kopen_p_Kclose :
      forall i K p,
        lcp p ->
        Kopen_p i (FCon K) (Kclose_p K i p) = p.

    Parameter Kclose_p_notin : forall K i p, K \notin Kfv_p (Kclose_p K i p).

    Parameter Ksubst_p_Kopen_comm :
      forall i X K U p,
        X <> K ->
        Kopen_p i (FCon K) (Ksubst_p X (FCon U) p) =
          Ksubst_p X (FCon U) (Kopen_p i (FCon K) p).

    Parameter Ksubst_p_intro :
      forall X U i p,
        X \notin Kfv_p p ->
        Kopen_p i U p = Ksubst_p X U (Kopen_p i (FCon X) p).

    Parameter Ksubst_p_fresh :
      forall K U p,
        K \notin Kfv_p p ->
        Ksubst_p K U p = p.

    Parameter notin_Kopen_p :
      forall i K p,
        K \notin Kfv_p (Kopen_p i (FCon K) p) ->
        Kopen_p i (FCon K) p = p.

    Parameter Kopen_p_notin_K :
      forall K i x p,
        K \notin Kfv_p (Kopen_p i (FCon x) p) ->
        K \notin Kfv_p p.

  End PATPROPS.

  Module SyntaxProps1 (PP : PATPROPS).
    Export PP.

    Lemma topen_neq :
      forall I J U V T,
        I <> J ->
        {I ~> U}({J ~> V}T) = {J ~> V}T ->
        {I ~> U}T = T.
    Proof.
      introv Hneq Heq. gen I J.
      solve_eq T; inverts* Heq.
    Qed.

    Lemma topen_lct :
      forall K U T,
        lct T ->
        {K ~> U}T = T.
    Proof.
      introv Hlct. gen K.
      solve_eq Hlct.
      - pick_fresh x.
        rewrite topen_neq with (J := 0) (V := TyFVar x);
          auto.
    Qed.

    Lemma tsubst_topen_distr :
      forall X U k T1 T2,
        lct U ->
        {X => U} ({k ~> T2}T1) = {k ~> {X => U}T2} ({X => U}T1).
    Proof.
      introv Hlct. gen k.
      solve_eq T1. rewrite* topen_lct.
    Qed.

    Lemma tsubst_fresh :
      forall X T U,
        X \notin tfv T ->
        {X => U}T = T.
    Proof. introv Hfv ; solve_eq T. Qed.

    Lemma tsubst_intro :
      forall X T U n,
        X \notin tfv T ->
        {n ~> U} T = {X => U}({n ~> TyFVar X}T).
    Proof. introv Hfv. gen n. solve_eq T. Qed.

    Lemma tsubst_topen_comm :
      forall X Y U T n,
        X <> Y ->
        lct U ->
        {n ~> TyFVar Y} ({X => U}T) = {X => U}({n ~> TyFVar Y} T).
    Proof.
      introv Hneq Hlct. gen n.
      solve_eq T ; rewrite* topen_lct.
    Qed.

    Lemma tsubst_lct :
      forall X U T,
        lct T ->
        lct U ->
        lct ({X => U}T).
    Proof.
      introv Hlct1 Hlct2.
      induction* Hlct1; solve_var.
      - apply_fresh* LCTAll.
        rewrite* tsubst_topen_comm.
    Qed.

    Lemma open_neq :
      forall i j u v t,
        i <> j ->
        [i ~> u]([j ~> v]t) = [j ~> v]t ->
        [i ~> u]t = t.
    Proof.
      introv Hneq Heq. gen i j. solve_eq t ; inverts* Heq.
    Qed.

    Lemma open_topen_neq :
      forall i u J V t,
        [i ~> u]([{J ~> V}]t) = [{J ~> V}] t ->
        [i ~> u]t = t.
    Proof.
      introv Heq. gen i J. solve_eq t ; inverts* Heq.
    Qed.

    Lemma open_Topen_rec :
      forall i u J V t,
        [i ~> u](Topen_t J V t) = Topen_t J V t ->
        [i ~> u]t = t.
    Proof.
      introv Heq. gen i J. solve_eq t ; inverts* Heq.
    Qed.

    Lemma open_Kopen_rec :
      forall i u J V t,
        [i ~> u](Kopen_t J V t) = Kopen_t J V t ->
        [i ~> u]t = t.
    Proof.
      introv Heq. gen i J. solve_eq t ; inverts* Heq.
    Qed.

    Lemma open_lc :
      forall k u t,
        lc t ->
        [k ~> u]t = t.
    Proof.
      introv Hlc. gen k.
      solve_eq Hlc.
      - pick_fresh x.
        rewrite open_neq with (j := 0) (v := TmFVar x);
          auto.
      - pick_fresh X.
        rewrite open_topen_neq with (J := 0) (V := TyFVar X);
          auto.
      - pick_fresh x.
        rewrite open_neq with (j := 0) (v := TmFVar x);
          auto.
      - pick_fresh X.
        rewrite open_Topen_rec with (J := 0) (V := FTName X);
          auto.
      - pick_fresh X.
        rewrite open_Kopen_rec with (J := 0) (V := FCon X);
          auto.
      - pick_fresh x.
        rewrite open_neq with (j := 0) (v := TmFVar x);
          auto.
    Qed.

    Lemma subst_open_distr :
      forall x u n t1 t2,
        lc u ->
        [x => u] ([n ~> t2] t1) = [n ~> [x => u]t2]([x => u]t1).
    Proof.
      introv Hlc. gen n.
      solve_eq t1. rewrite* open_lc.
    Qed.

    Lemma subst_open_comm :
      forall x y n u t,
        x <> y ->
        lc u ->
        [n ~> TmFVar y]([x => u]t) = [x => u] ([n ~> TmFVar y]t).
    Proof.
      introv Hneq Hlc. gen n.
      solve_eq t. apply* open_lc.
    Qed.

    Lemma subst_fresh :
      forall x t u,
        x \notin fv t ->
        [x => u]t = t.
    Proof. solve_eq t. Qed.

    Lemma subst_intro :
      forall x t u n,
        x \notin fv t ->
        [n ~> u] t = [x => u]([n ~> TmFVar x]t).
    Proof. introv Hfv. gen n. solve_eq t. Qed.

    Lemma tsubst_t_topen_distr :
      forall X U n T t,
        lct U ->
        [{X => U}] ([{n ~> T}] t) = [{n ~> {X => U}T}] ([{X => U}]t).
    Proof.
      introv Hlct.
      gen n. solve_eq t ;
        apply* tsubst_topen_distr.
    Qed.

    Lemma tsubst_t_fresh :
      forall X t U,
        X \notin tfv_t t ->
        [{X => U}]t = t.
    Proof.
      introv Hfv.
      solve_eq t; apply* tsubst_fresh.
    Qed.

    Lemma tsubst_t_intro :
      forall X U t,
        X \notin tfv_t t ->
        lct U ->
        [{0 ~> U}]t = [{X => U}] ([{0 ~> TyFVar X}]t).
    Proof.
      introv Hftv Hlc.
      rewrite* tsubst_t_topen_distr.
      solve_var. rewrite* tsubst_t_fresh.
    Qed.

    Lemma topen_open_rec :
      forall i j T t u,
        [{i ~> T}] ([j ~> u] t) = [j ~> u]t ->
        [{i ~> T}] t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq.
    Qed.

    Lemma topen_t_neq :
      forall I J T U t,
        I <> J ->
        [{I ~> T}] ([{J ~> U}] t) = [{J ~> U}] t ->
        [{I ~> T}]t = t.
    Proof.
      introv Hneq Heq. gen I J.
      solve_eq t ; inverts* Heq; eauto using topen_neq.
    Qed.

    Lemma topen_Topen_rec :
      forall i j T U T',
        {i ~> T} (Topen_ty j T' U) = Topen_ty j T' U ->
        {i ~> T}U = U.
    Proof.
      introv Heq. gen i.
      solve_eq U ; inverts* Heq.
    Qed.

    Lemma topen_t_Topen_rec :
      forall i j T t T',
        [{i ~> T}] (Topen_t j T' t) = Topen_t j T' t ->
        [{i ~> T}]t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq ; apply* topen_Topen_rec.
    Qed.

    Lemma topen_Kopen_rec :
      forall i j T U K,
        {i ~> T} (Kopen_ty j K U) = Kopen_ty j K U ->
        {i ~> T}U = U.
    Proof.
      introv Heq. gen i.
      solve_eq U ; inverts* Heq.
    Qed.

    Lemma topen_t_Kopen_rec :
      forall i j T t K,
        [{i ~> T}] (Kopen_t j K t) = Kopen_t j K t ->
        [{i ~> T}]t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq ; apply* topen_Kopen_rec.
    Qed.

    Lemma topen_t_lc :
      forall X t n,
        lc t ->
        [{n ~> TyFVar X}]t = t.
    Proof.
      introv Hlc. gen n.
      solve_eq Hlc ; try solve [ rewrite~ topen_lct ] ; pick_fresh_gen L x.
      - apply* topen_open_rec.
      - apply* (topen_t_neq (S n) 0 (TyFVar X) (TyFVar x)).
      - apply* topen_open_rec.
      - apply* topen_t_Topen_rec.
      - apply topen_neq with (J := 0) (V := TyFVar x) ; auto.
        apply* topen_lct.
      - apply* topen_t_Kopen_rec.
      - apply* topen_open_rec.
    Qed.

    Lemma topen_t_subst_comm :
      forall X x n t1 t2,
        X \notin tfv_t t2 ->
        lc t2 ->
        [{n ~> TyFVar X}] ([x => t2]t1) = [x => t2]([{n ~> TyFVar X}] t1).
    Proof.
      introv Hnin Hlc. gen n.
      solve_eq t1. rewrite* topen_t_lc.
    Qed.

    Lemma tsubst_t_open_comm :
      forall X x n U t,
        [n ~> TmFVar x] ([{X => U}]t) = [{X => U}] ([n ~> TmFVar x]t).
    Proof. intros. gen n. solve_eq t. Qed.

    Lemma open_notin :
      forall t X y n,
        X \notin tfv_t ([n ~> TmFVar y]t) ->
        X \notin tfv_t t.
    Proof.
      introv Hnin. gen n.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end ; eauto.
    Qed.

    Lemma topen_notin :
      forall T X Y n,
        X \notin tfv ({n ~> TyFVar Y}T) ->
        X \notin tfv T.
    Proof.
      introv Hnin. gen n.
      induction T; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end ; eauto.
    Qed.

    Lemma topen_t_notin :
      forall t X Y n,
        X \notin tfv_t ([{n ~> TyFVar Y}]t) ->
        X \notin tfv_t t.
    Proof with eauto using topen_notin.
      introv Hnin. gen n.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma Topen_ty_notin :
      forall ty X Y n,
        X \notin tfv (Topen_ty n (FTName Y) ty) ->
        X \notin tfv ty.
    Proof.
      introv Hnin. gen n.
      induction ty; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end ; eauto.
    Qed.

    Lemma Topen_t_notin :
      forall t X Y n,
        X \notin tfv_t (Topen_t n (FTName Y) t) ->
        X \notin tfv_t t.
    Proof with eauto using Topen_ty_notin.
      introv Hnin. gen n.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma Kopen_ty_notin :
      forall ty X Y n,
        X \notin tfv (Kopen_ty n (FCon Y) ty) ->
        X \notin tfv ty.
    Proof.
      introv Hnin. gen n.
      induction ty; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end ; eauto.
    Qed.

    Lemma Kopen_t_notin :
      forall t X Y n,
        X \notin tfv_t (Kopen_t n (FCon Y) t) ->
        X \notin tfv_t t.
    Proof with eauto using Kopen_ty_notin.
      introv Hnin. gen n.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma topen_t_tsubst_comm :
      forall X Y T n t,
        X <> Y ->
        lct T ->
        [{n ~> TyFVar Y}] ([{X => T}]t) =
          [{X => T}]([{n ~> TyFVar Y}] t).
    Proof.
      introv Hneq Hlct. gen n.
      solve_eq t ; rewrite* tsubst_topen_comm.
    Qed.

    Lemma Topen_neq :
      forall i j T T' T0,
        i <> j ->
        Topen i T (Topen j T' T0) = Topen j T' T0 ->
        Topen i T T0 = T0.
    Proof. introv Hneq Heq. solve_eq T0. Qed.

    Lemma Topen_d_lcd :
      forall j T d,
        lcd d ->
        Topen_d j T d = d.
    Proof.
      introv Hlcd.
      solve_eq Hlcd. unfolds Topen_d. rew_listx.
      destruct x. destruct H.
      inverts H. rewrite~ IHHlcd.
    Qed.

    Lemma Topen_d_neq :
      forall i j T T' d,
        i <> j ->
        Topen_d i T (Topen_d j T' d) = Topen_d j T' d ->
        Topen_d i T d = d.
    Proof.
      introv Hneq Heq. unfolds Topen_d.
      induction~ d.
      rew_listx in *. destruct a. inverts Heq.
      rewrite Topen_neq with (j := j) (T' := T') ; auto.
      rewrite~ IHd.
    Qed.

    Lemma Topen_Kopen_d_rec :
      forall i j T K d,
        Topen_d i T (Kopen_d j K d) = Kopen_d j K d ->
        Topen_d i T d = d.
    Proof.
      introv Heq. unfolds Topen_d. unfolds Kopen_d.
      induction~ d.
      rew_listx in *. destruct a. injection Heq ; intros. rewrite H0.
      rewrite~ IHd.
    Qed.

    Lemma Topen_k_lck :
      forall j T k,
        lck k ->
        Topen_k j T k = k.
    Proof.
      introv Hlck. solve_eq Hlck. rewrite~ Topen_d_lcd.
    Qed.

    Lemma Topen_k_neq :
      forall i j T T' k,
        i <> j ->
        Topen_k i T (Topen_k j T' k) = Topen_k j T' k ->
        Topen_k i T k = k.
    Proof.
      introv Hneq Heq.
      solve_eq k. inverts Heq. apply Topen_d_neq with (j := j) (T' := T') ; auto.
    Qed.

    Lemma Topen_Kopen_k_rec :
      forall i j T K k,
        Topen_k i T (Kopen_k j K k) = Kopen_k j K k ->
        Topen_k i T k = k.
    Proof.
      introv Heq. solve_eq k ; inverts Heq. apply* Topen_Kopen_d_rec.
    Qed.

    Lemma Topen_topen_rec :
      forall i j T U ty,
        Topen_ty i T ({j ~> U} ty) = {j ~> U}ty ->
        Topen_ty i T ty = ty.
    Proof.
      introv Heq. gen j.
      solve_eq ty ; inverts* Heq.
    Qed.

    Lemma Topen_ty_lct :
      forall k T ty,
        lct ty ->
        Topen_ty k T ty = ty.
    Proof.
      introv Hlct.
      solve_eq Hlct ;
        try solve [ apply* Topen_d_lcd
                  | apply* Topen_k_lck ] ;
        pick_fresh_gen L x.
      - apply* Topen_topen_rec.
    Qed.

    Lemma Topen_ty_neq :
      forall i j T T' ty,
        i <> j ->
        Topen_ty i T (Topen_ty j T' ty) = Topen_ty j T' ty ->
        Topen_ty i T ty = ty.
    Proof.
      introv Hneq Heq. gen i j.
      solve_eq ty ; inverts* Heq.
      - apply Topen_k_neq with (j := j) (T' := T') ; auto.
      - apply Topen_neq with (j := j) (T' := T') ; auto.
      - apply Topen_d_neq with (j := j) (T' := T') ; auto.
    Qed.

    Lemma Topen_Kopen_ty_rec :
      forall i j T K ty,
        Topen_ty i T (Kopen_ty j K ty) = Kopen_ty j K ty ->
        Topen_ty i T ty = ty.
    Proof.
      introv Heq.
      solve_eq ty ; inverts* Heq.
      - apply* Topen_Kopen_k_rec.
      - apply* Topen_Kopen_d_rec.
    Qed.

    Lemma Topen_open_rec :
      forall i j T u t,
        Topen_t i T ([j ~> u] t) = [j ~> u]t ->
        Topen_t i T t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq.
    Qed.

    Lemma Topen_topen_t_rec :
      forall i j T ty t,
        Topen_t i T ([{j ~> ty}] t) = [{j ~> ty}] t ->
        Topen_t i T t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq ; apply* Topen_topen_rec.
    Qed.

    Lemma Topen_t_neq :
      forall i j T T' t,
        i <> j ->
        Topen_t i T (Topen_t j T' t) = Topen_t j T' t ->
        Topen_t i T t = t.
    Proof.
      introv Hneq Heq. gen i j.
      solve_eq t ; inverts* Heq ;
        solve [ apply Topen_neq with (j := j) (T' := T') ; auto
              | apply Topen_d_neq with (j := j) (T' := T') ; auto
              | apply Topen_k_neq with (j := j) (T' := T') ; auto
              | apply Topen_ty_neq with (j := j) (T' := T') ; auto ].
    Qed.

    Lemma Topen_Kopen_t_rec :
      forall i j T K t,
        Topen_t i T (Kopen_t j K t) = Kopen_t j K t ->
        Topen_t i T t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq ;
        solve [ apply* Topen_Kopen_d_rec
              | apply* Topen_Kopen_k_rec
              | apply* Topen_Kopen_ty_rec ].
    Qed.

    Lemma Topen_t_lc :
      forall k T t,
        lc t ->
        Topen_t k T t = t.
    Proof.
      introv Hlc. gen k.
      solve_eq Hlc ;
        try solve [ apply* Topen_d_lcd
                  | apply* Topen_k_lck
                  | apply* Topen_ty_lct ] ;
        pick_fresh_gen L x.
      - apply* Topen_open_rec.
      - apply* Topen_topen_t_rec.
      - apply* Topen_open_rec.
      - apply* (Topen_t_neq (S k) 0 T (FTName x)).
      - apply* Topen_topen_rec.
        apply* Topen_ty_lct.
      - apply* Topen_Kopen_t_rec.
      - apply* Topen_open_rec.
    Qed.

    Lemma Topen_t_subst_comm :
      forall x n T t1 t2,
        lc t2 ->
        Topen_t n T ([x => t2]t1) = [x => t2] (Topen_t n T t1).
    Proof.
      introv Hlc. gen n. solve_eq t1. apply* Topen_t_lc.
    Qed.

    Lemma Topen_tsubst_comm :
      forall X n T U ty,
        lct U ->
        Topen_ty n T ({X => U}ty) = {X => U} (Topen_ty n T ty).
    Proof.
      introv Hlct. gen n. solve_eq ty ; apply* Topen_ty_lct.
    Qed.

    Lemma Topen_t_tsubst_comm :
      forall X n T U t,
        lct U ->
        Topen_t n T ([{X => U}]t) = [{X => U}] (Topen_t n T t).
    Proof.
      introv Hlc. gen n. solve_eq t ; apply* Topen_tsubst_comm.
    Qed.


    Lemma Kopen_d_lcd :
      forall j T d,
        lcd d ->
        Kopen_d j T d = d.
    Proof.
      introv Hlcd.
      solve_eq Hlcd. unfolds Kopen_d. rew_listx.
      destruct x. destruct H. rewrite~ IHHlcd.
      induction~ l0. rew_listx in *. destruct H0. inverts H0. simpls.
      apply IHl0 in H1. injection H1 ; intros. rewrite* H0.
    Qed.

    Lemma Kopen_d_neq :
      forall i j K K' d,
        i <> j ->
        Kopen_d i K (Kopen_d j K' d) = Kopen_d j K' d ->
        Kopen_d i K d = d.
    Proof.
      introv Hneq Heq. unfolds Kopen_d.
      induction~ d.
      rew_listx in *. destruct a. inverts Heq.
      rewrite~ IHd. repeat fequals.
      induction~ l. rew_listx in *. inverts H0. rewrite~ IHl.
      fequals~. destruct a ; solve_var.
    Qed.

    Lemma Kopen_Topen_d_rec :
      forall i j T K d,
        Kopen_d i K (Topen_d j T d) = Topen_d j T d ->
        Kopen_d i K d = d.
    Proof.
      introv Heq. unfolds Kopen_d. unfolds Topen_d.
      induction~ d.
      rew_listx in *. destruct a. injection Heq ; intros. rewrite H0.
      rewrite~ IHd.
    Qed.

    Lemma Kopen_k_lck :
      forall j T k,
        lck k ->
        Kopen_k j T k = k.
    Proof.
      introv Hlck. solve_eq Hlck. rewrite~ Kopen_d_lcd.
    Qed.

    Lemma Kopen_k_neq :
      forall i j K K' k,
        i <> j ->
        Kopen_k i K (Kopen_k j K' k) = Kopen_k j K' k ->
        Kopen_k i K k = k.
    Proof.
      introv Hneq Heq.
      solve_eq k. inverts Heq. apply Kopen_d_neq with (j := j) (K' := K') ; auto.
    Qed.

    Lemma Kopen_Topen_k_rec :
      forall i j T K k,
        Kopen_k i K (Topen_k j T k) = Topen_k j T k ->
        Kopen_k i K k = k.
    Proof.
      introv Heq. solve_eq k ; inverts Heq. apply* Kopen_Topen_d_rec.
    Qed.

    Lemma Kopen_topen_rec :
      forall i j T U ty,
        Kopen_ty i T ({j ~> U} ty) = {j ~> U}ty ->
        Kopen_ty i T ty = ty.
    Proof.
      introv Heq. gen j.
      solve_eq ty ; inverts* Heq.
    Qed.

    Lemma Kopen_ty_lct :
      forall k T ty,
        lct ty ->
        Kopen_ty k T ty = ty.
    Proof.
      introv Hlct.
      solve_eq Hlct ;
        try solve [ apply* Kopen_d_lcd
                  | apply* Kopen_k_lck ].
      - pick_fresh_gen L x. apply* Kopen_topen_rec.
      - induction~ ps. rew_listx in *. destruct H. fequals~.
        apply* Kopen_p_lcp.
    Qed.

    Lemma Kopen_ty_neq :
      forall i j K K' ty,
        i <> j ->
        Kopen_ty i K (Kopen_ty j K' ty) = Kopen_ty j K' ty ->
        Kopen_ty i K ty = ty.
    Proof.
      introv Hneq Heq. gen i j.
      solve_eq ty ; inverts* Heq.
      - apply Kopen_k_neq with (j := j) (K' := K') ; auto.
      - induction~ l. rew_listx in *. inverts H2. fequals~.
        apply Kopen_p_neq with (j := j) (K' := K') ; auto.
      - apply Kopen_d_neq with (j := j) (K' := K') ; auto.
    Qed.

    Lemma Kopen_Topen_ty_rec :
      forall i j T K ty,
        Kopen_ty i K (Topen_ty j T ty) = Topen_ty j T ty ->
        Kopen_ty i K ty = ty.
    Proof.
      introv Heq.
      solve_eq ty ; inverts* Heq.
      - apply* Kopen_Topen_k_rec.
      - apply* Kopen_Topen_d_rec.
    Qed.

    Lemma Kopen_open_rec :
      forall i j T u t,
        Kopen_t i T ([j ~> u] t) = [j ~> u]t ->
        Kopen_t i T t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq.
    Qed.

    Lemma Kopen_topen_t_rec :
      forall i j T ty t,
        Kopen_t i T ([{j ~> ty}] t) = [{j ~> ty}] t ->
        Kopen_t i T t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq ; apply* Kopen_topen_rec.
    Qed.

    Lemma Kopen_t_neq :
      forall i j K K' t,
        i <> j ->
        Kopen_t i K (Kopen_t j K' t) = Kopen_t j K' t ->
        Kopen_t i K t = t.
    Proof.
      introv Hneq Heq. gen i j.
      solve_eq t ; inverts* Heq ;
        try solve [ apply Kopen_d_neq with (j := j) (K' := K') ; auto
                  | apply Kopen_k_neq with (j := j) (K' := K') ; auto
                  | apply Kopen_ty_neq with (j := j) (K' := K') ; auto
                  | apply Kopen_p_neq with (j := j) (K' := K') ; auto].
      destruct c ; solve_var.
    Qed.

    Lemma Kopen_Topen_t_rec :
      forall i j T K t,
        Kopen_t i K (Topen_t j T t) = Topen_t j T t ->
        Kopen_t i K t = t.
    Proof.
      introv Heq. gen i j.
      solve_eq t ; inverts* Heq ;
        solve [ apply* Kopen_Topen_d_rec
              | apply* Kopen_Topen_k_rec
              | apply* Kopen_Topen_ty_rec ].
    Qed.

    Lemma Kopen_t_lc :
      forall k K t,
        lc t ->
        Kopen_t k K t = t.
    Proof.
      introv Hlc. gen k.
      solve_eq Hlc ;
        try solve [ apply* Kopen_d_lcd
                  | apply* Kopen_k_lck
                  | apply* Kopen_ty_lct
                  | apply* Kopen_p_lcp ] ;
        pick_fresh_gen L x.
      - apply* Kopen_open_rec.
      - apply* Kopen_topen_t_rec.
      - apply* Kopen_open_rec.
      - apply* Kopen_Topen_t_rec.
      - apply* Kopen_topen_rec.
        apply* Kopen_ty_lct.
      - apply* (Kopen_t_neq (S k) 0 K (FCon x)).
      - apply* Kopen_open_rec.
    Qed.

    Lemma Kopen_t_subst_comm :
      forall x n K t1 t2,
        lc t2 ->
        Kopen_t n K ([x => t2]t1) = [x => t2] (Kopen_t n K t1).
    Proof.
      introv Hlc. gen n. solve_eq t1 ; apply* Kopen_t_lc.
    Qed.

    Lemma Kopen_tsubst_comm :
      forall X n T U ty,
        lct U ->
        Kopen_ty n T ({X => U}ty) = {X => U} (Kopen_ty n T ty).
    Proof.
      introv Hlct. gen n. solve_eq ty ; apply* Kopen_ty_lct.
    Qed.

    Lemma Kopen_t_tsubst_comm :
      forall X n T U t,
        lct U ->
        Kopen_t n T ([{X => U}]t) = [{X => U}] (Kopen_t n T t).
    Proof.
      introv Hlc. gen n. solve_eq t ; apply* Kopen_tsubst_comm.
    Qed.

    Lemma Topen_t_open_comm :
      forall i n T v t,
        lc v ->
        Topen_t i T ([n ~> v] t) = [n ~> v] (Topen_t i T t).
    Proof.
      introv Hlc. gen n i. solve_eq t. apply* Topen_t_lc.
    Qed.

    Lemma Tclose_d_fresh :
      forall T i d,
        T \notin Tfv_d d ->
        Tclose_d T i d = d.
    Proof.
      introv Hfv. unfolds Tclose_d. unfolds Tfv_d.
      induction~ d. rew_listx in *. simpls. destruct a.
      fequals~. destruct t ; solve_var.
    Qed.

    Lemma Tclose_k_fresh :
      forall T i k,
        T \notin Tfv_k k ->
        Tclose_k T i k = k.
    Proof. introv Hfv. solve_eq k ; apply~ Tclose_d_fresh. Qed.

    Lemma Tclose_ty_fresh :
      forall T i ty,
        T \notin Tfv_ty ty ->
        Tclose_ty T i ty = ty.
    Proof.
      introv Hfv. solve_eq ty.
      - apply~ Tclose_k_fresh.
      - destruct t ; solve_var.
      - apply~ Tclose_d_fresh.
    Qed.

    Lemma Tclose_t_fresh :
      forall T i t,
        T \notin Tfv_t t ->
        Tclose_t T i t = t.
    Proof.
      introv Hfv. gen i. solve_eq t ;
        try solve [ apply~ Tclose_d_fresh
                  | apply~ Tclose_k_fresh
                  | apply~ Tclose_ty_fresh ].
      destruct t0 ; solve_var.
    Qed.

    Lemma Tclose_t_open_comm :
      forall i n T v t,
        T \notin Tfv_t v ->
        Tclose_t T i ([n ~> v] t) = [n ~> v] (Tclose_t T i t).
    Proof.
      introv. gen i n. solve_eq t ; apply* Tclose_t_fresh.
    Qed.

    Lemma Topen_ty_topen_comm :
      forall i n T ty1 ty2,
        lct ty1 ->
        Topen_ty i T ({n ~> ty1} ty2) = {n ~> ty1} (Topen_ty i T ty2).
    Proof.
      introv. gen n. solve_eq ty2. apply* Topen_ty_lct.
    Qed.

    Lemma Topen_t_topen_comm :
      forall i n T ty t,
        lct ty ->
        Topen_t i T ([{n ~> ty}] t) = [{n ~> ty}] (Topen_t i T t).
    Proof.
      introv. gen n i. solve_eq t ; apply* Topen_ty_topen_comm.
    Qed.

    Lemma Tclose_ty_topen_comm :
      forall i n T ty1 ty2,
        T \notin Tfv_ty ty1 ->
        Tclose_ty T i ({n ~> ty1} ty2) = {n ~> ty1} (Tclose_ty T i ty2).
    Proof.
      introv. gen n. solve_eq ty2 ; apply* Tclose_ty_fresh.
    Qed.

    Lemma Tclose_t_topen_comm :
      forall i n T ty t,
        T \notin Tfv_ty ty ->
        Tclose_t T i ([{n ~> ty}] t) = [{n ~> ty}] (Tclose_t T i t).
    Proof.
      introv. gen n i. solve_eq t ; apply* Tclose_ty_topen_comm.
    Qed.

    Lemma Topen_d_Topen_comm :
      forall i j T T' d,
        i <> j ->
        Topen_d i (FTName T) (Topen_d j (FTName T') d) =
          Topen_d j (FTName T') (Topen_d i (FTName T) d).
    Proof.
      introv Hneq. unfolds Topen_d.
      induction~ d. destruct a. rew_listx. rewrite~ IHd.
      destruct t ; solve_var.
    Qed.

    Lemma Topen_k_Topen_comm :
      forall i j T T' k,
        i <> j ->
        Topen_k i (FTName T) (Topen_k j (FTName T') k) =
          Topen_k j (FTName T') (Topen_k i (FTName T) k).
    Proof. introv Hneq. solve_eq k ; apply~ Topen_d_Topen_comm. Qed.

    Lemma Topen_ty_Topen_comm :
      forall i j T T' ty,
        i <> j ->
        Topen_ty i (FTName T) (Topen_ty j (FTName T') ty) =
          Topen_ty j (FTName T') (Topen_ty i (FTName T) ty).
    Proof.
      introv Hneq. solve_eq ty.
      - apply~ Topen_k_Topen_comm.
      - destruct t ; solve_var.
      - apply~ Topen_d_Topen_comm.
    Qed.

    Lemma Topen_t_Topen_comm :
      forall i j T T' t,
        i <> j ->
        Topen_t i (FTName T) (Topen_t j (FTName T') t) =
          Topen_t j (FTName T') (Topen_t i (FTName T) t).
    Proof.
      introv Hneq. gen i j. solve_eq t ;
        try solve [ apply~ Topen_d_Topen_comm
                  | apply~ Topen_k_Topen_comm
                  | apply~ Topen_ty_Topen_comm ].
      destruct t0 ; solve_var.
    Qed.

    Lemma Topen_d_Tclose_comm :
      forall i j T T' d,
        i <> j ->
        T <> T' ->
        Topen_d i (FTName T) (Tclose_d T' j d) =
          Tclose_d T' j (Topen_d i (FTName T) d).
    Proof.
      introv Hneq1 Hneq2. unfolds Topen_d. unfolds Tclose_d.
      induction~ d. destruct a. rew_listx. rewrite~ IHd.
      destruct t ; solve_var.
    Qed.

    Lemma Topen_k_Tclose_comm :
      forall i j T T' k,
        i <> j ->
        T <> T' ->
        Topen_k i (FTName T) (Tclose_k T' j k) =
          Tclose_k T' j (Topen_k i (FTName T) k).
    Proof. intros. solve_eq k ; apply~ Topen_d_Tclose_comm. Qed.

    Lemma Topen_ty_Tclose_comm :
      forall i j T T' ty,
        i <> j ->
        T <> T' ->
        Topen_ty i (FTName T) (Tclose_ty T' j ty) =
          Tclose_ty T' j (Topen_ty i (FTName T) ty).
    Proof.
      introv Hneq1 Hneq2. solve_eq ty.
      - apply~ Topen_k_Tclose_comm.
      - destruct t ; solve_var.
      - apply~ Topen_d_Tclose_comm.
    Qed.

    Lemma Topen_t_Tclose_comm :
      forall i j T T' t,
        i <> j ->
        T <> T' ->
        Topen_t i (FTName T) (Tclose_t T' j t) = Tclose_t T' j (Topen_t i (FTName T) t).
    Proof.
      introv Hneq1 Hneq2. gen i j. solve_eq t ;
        try solve [ apply~ Topen_d_Tclose_comm
                  | apply~ Topen_k_Tclose_comm
                  | apply~ Topen_ty_Tclose_comm ].
      destruct t0 ; solve_var.
    Qed.

    Lemma Kopen_d_Topen_comm :
      forall i j K T d,
        Kopen_d i K (Topen_d j T d) = Topen_d j T (Kopen_d i K d).
    Proof.
      intros. unfolds Topen_d. unfolds Kopen_d.
      induction~ d. destruct a. rew_listx. rewrite~ IHd.
    Qed.

    Lemma Kopen_k_Topen_comm :
      forall i j K T k,
        Kopen_k i K (Topen_k j T k) = Topen_k j T (Kopen_k i K k).
    Proof. intros. solve_eq k ; apply~ Kopen_d_Topen_comm. Qed.

    Lemma Kopen_ty_Topen_comm :
      forall i j K T ty,
        Kopen_ty i K (Topen_ty j T ty) = Topen_ty j T (Kopen_ty i K ty).
    Proof.
      intros. solve_eq ty.
      - apply~ Kopen_k_Topen_comm.
      - apply~ Kopen_d_Topen_comm.
    Qed.

    Lemma Kopen_t_Topen_comm :
      forall i j K T t,
        Kopen_t i K (Topen_t j T t) = Topen_t j T (Kopen_t i K t).
    Proof.
      intros. gen i j. solve_eq t ;
        try solve [ apply~ Kopen_d_Topen_comm
                  | apply~ Kopen_k_Topen_comm
                  | apply~ Kopen_ty_Topen_comm ].
    Qed.

    Lemma Kopen_d_Tclose_comm :
      forall i j K T d,
        Kopen_d i K (Tclose_d T j d) = Tclose_d T j (Kopen_d i K d).
    Proof.
      intros. unfolds Tclose_d. unfolds Kopen_d.
      induction~ d. destruct a. rew_listx. rewrite~ IHd.
    Qed.

    Lemma Kopen_k_Tclose_comm :
      forall i j K T k,
        Kopen_k i K (Tclose_k T j k) = Tclose_k T j (Kopen_k i K k).
    Proof. intros. solve_eq k ; apply~ Kopen_d_Tclose_comm. Qed.

    Lemma Kopen_ty_Tclose_comm :
      forall i j K T ty,
        Kopen_ty i K (Tclose_ty T j ty) = Tclose_ty T j (Kopen_ty i K ty).
    Proof.
      intros. solve_eq ty.
      - apply~ Kopen_k_Tclose_comm.
      - apply~ Kopen_d_Tclose_comm.
    Qed.

    Lemma Kopen_t_Tclose_comm :
      forall i j K T t,
        Kopen_t i K (Tclose_t T j t) = Tclose_t T j (Kopen_t i K t).
    Proof.
      intros. gen i j. solve_eq t ;
        try solve [ apply~ Kopen_d_Tclose_comm
                  | apply~ Kopen_k_Tclose_comm
                  | apply~ Kopen_ty_Tclose_comm ].
    Qed.

    Lemma open_inj :
      forall i x t1 t2,
        x \notin fv t1 \u fv t2 ->
        [i ~> TmFVar x] t1 = [i ~> TmFVar x] t2 ->
        t1 = t2.
    Proof.
      introv Hfv Heq. gen i t2.
      solve_eq t1 ; destruct t2 ; inverts Heq ; solve_var ; fequals*.
      - inverts H0. notin_false.
    Qed.

    Lemma topen_inj :
      forall i x ty1 ty2,
        x \notin tfv ty1 \u tfv ty2 ->
        {i ~> TyFVar x} ty1 = {i ~> TyFVar x} ty2 ->
        ty1 = ty2.
    Proof.
      introv Hfv Heq. gen i ty2.
      solve_eq ty1 ; destruct ty2 ; inverts Heq ; solve_var ; fequals*.
      - inverts H0. notin_false.
    Qed.

    Lemma topen_t_inj :
      forall i x t1 t2,
        x \notin tfv_t t1 \u tfv_t t2 ->
        [{i ~> TyFVar x}] t1 = [{i ~> TyFVar x}] t2 ->
        t1 = t2.
    Proof.
      introv Hfv Heq. gen i t2.
      solve_eq t1 ; destruct t2 ; inverts Heq ; solve_var ; fequals* ;
        rewrite_all notin_union in Hfv ; apply* topen_inj.
    Qed.

    Lemma Topen_d_inj :
      forall i X d1 d2,
        X \notin Tfv_d d1 \u Tfv_d d2 ->
        Topen_d i (FTName X) d1 = Topen_d i (FTName X) d2 ->
        d1 = d2.
    Proof.
      introv. gen d2. unfolds Topen_d. unfolds Tfv_d.
      induction d1 ; introv Hfv Heq ; destruct d2 ; inverts~ Heq.
      destruct a ; destruct p ; rew_listx in * ; simpls.
      do 2 fequals~. inverts H0.
      destruct t ; destruct t0 ; solve_var ; inverts H2 ; notin_false.
    Qed.

    Lemma Topen_k_inj :
      forall i X k1 k2,
        X \notin Tfv_k k1 \u Tfv_k k2 ->
        Topen_k i (FTName X) k1 = Topen_k i (FTName X) k2 ->
        k1 = k2.
    Proof.
      introv Hfv Heq. gen k2.
      solve_eq k1 ; destruct k2 ; inverts Heq ; fequals ; apply* Topen_d_inj.
    Qed.

    Lemma Topen_ty_inj :
      forall i X ty1 ty2,
        X \notin Tfv_ty ty1 \u Tfv_ty ty2 ->
        Topen_ty i (FTName X) ty1 = Topen_ty i (FTName X) ty2 ->
        ty1 = ty2.
    Proof.
      introv Hfv Heq. gen i ty2.
      solve_eq ty1 ; destruct ty2 ; inverts Heq ; solve_var ; fequals* ;
        rewrite_all notin_union in Hfv.
      - apply* Topen_k_inj.
      - destruct Hfv as ((?&Hfv1)&(?&Hfv2)).
        destruct t ; destruct t0 ; solve_var ; inverts H1 ; notin_false.
      - apply* Topen_d_inj.
    Qed.

    Lemma Topen_t_inj :
      forall i X t1 t2,
        X \notin Tfv_t t1 \u Tfv_t t2 ->
        Topen_t i (FTName X) t1 = Topen_t i (FTName X) t2 ->
        t1 = t2.
    Proof.
      introv Hfv Heq. gen i t2.
      solve_eq t1 ; destruct t2 ; inverts Heq ; solve_var ; fequals* ;
        rewrite_all notin_union in Hfv ;
        try solve [ apply* Topen_d_inj
                  | apply* Topen_k_inj
                  | apply* Topen_ty_inj ].
      destruct Hfv as ((?&?&Hfv1&?)&(?&?&Hfv2&?)).
      destruct t0 ; destruct t3 ; solve_var ; inverts H2 ; notin_false.
    Qed.

    Lemma Kopen_d_inj :
      forall i X d1 d2,
        X \notin Kfv_d d1 \u Kfv_d d2 ->
        Kopen_d i (FCon X) d1 = Kopen_d i (FCon X) d2 ->
        d1 = d2.
    Proof.
      introv. gen d2. unfolds Kopen_d. unfolds Kfv_d.
      induction d1 ; introv Hfv Heq ; destruct d2 ; inverts~ Heq.
      destruct a ; destruct p ; rew_listx in * ; simpls.
      fequals~. fequals. inverts H0.
      gen l0. induction l ; introv Hfv Heq ; destruct l0 ; inverts~ Heq.
      rew_listx in * ; simpls ; fequals~.
      destruct a ; destruct c ; solve_var ; inverts H0 ; notin_false.
    Qed.

    Lemma Kopen_k_inj :
      forall i X k1 k2,
        X \notin Kfv_k k1 \u Kfv_k k2 ->
        Kopen_k i (FCon X) k1 = Kopen_k i (FCon X) k2 ->
        k1 = k2.
    Proof.
      introv Hfv Heq. gen k2.
      solve_eq k1 ; destruct k2 ; inverts Heq ; fequals ; apply* Kopen_d_inj.
    Qed.

    Lemma Kopen_ty_inj :
      forall i X ty1 ty2,
        X \notin Kfv_ty ty1 \u Kfv_ty ty2 ->
        Kopen_ty i (FCon X) ty1 = Kopen_ty i (FCon X) ty2 ->
        ty1 = ty2.
    Proof.
      introv Hfv Heq. gen i ty2.
      solve_eq ty1 ; destruct ty2 ; inverts Heq ; solve_var ; fequals* ;
        rewrite_all notin_union in Hfv.
      - apply* Kopen_k_inj.
      - gen l0. induction l ; intros ; rew_listx in H2.
        + erewrite* map_eq_nil_inv.
        + forwards* (x1&t1&?&?&?): map_eq_cons_inv. substs.
          rew_listx in * ; simpls. inverts H2. fequals*.
          rewrite notin_union in Hfv. apply* Kopen_p_inj.
      - apply* Kopen_d_inj.
    Qed.

    Lemma Kopen_t_inj :
      forall i X t1 t2,
        X \notin Kfv_t t1 \u Kfv_t t2 ->
        Kopen_t i (FCon X) t1 = Kopen_t i (FCon X) t2 ->
        t1 = t2.
    Proof.
      introv Hfv Heq. gen i t2.
      solve_eq t1 ; destruct t2 ; inverts Heq ; solve_var ; fequals* ;
        rewrite_all notin_union in Hfv ;
        try solve [ apply* Kopen_d_inj
                  | apply* Kopen_k_inj
                  | apply* Kopen_ty_inj
                  | apply* Kopen_p_inj ].
      destruct Hfv as ((Hfv1&?&?)&(Hfv2&?&?)).
      destruct c ; destruct c0 ; solve_var ; inverts H0 ; notin_false.
    Qed.

    Lemma Topen_d_Tclose :
      forall i T d,
        lcd d ->
        Topen_d i (FTName T) (Tclose_d T i d) = d.
    Proof.
      introv Hlc. unfolds lcd. unfolds Topen_d. unfolds Tclose_d.
      induction~ Hlc. rew_listx. destruct x. do 2 fequals.
      destruct H as (HlcT&?).
      destruct t ; solve_var ; inverts HlcT ; discriminate.
    Qed.

    Lemma Topen_k_Tclose :
      forall i T k,
        lck k ->
        Topen_k i (FTName T) (Tclose_k T i k) = k.
    Proof. introv Hlc. solve_eq Hlc. apply~ Topen_d_Tclose. Qed.

    Lemma Topen_ty_Tclose :
      forall i T ty,
        lct ty ->
        Topen_ty i (FTName T) (Tclose_ty T i ty) = ty.
    Proof.
      introv Hlc. solve_eq Hlc.
      - apply~ Topen_k_Tclose.
      - remember (Topen_ty i (FTName T) (Tclose_ty T i T0)).
        pick_fresh X ; substs. applys~ topen_inj 0 X.
        rewrite* <- Topen_ty_topen_comm. rewrite* <- Tclose_ty_topen_comm. simpls~.
      - apply~ Topen_d_Tclose.
    Qed.

    Lemma Topen_t_Tclose :
      forall i T t,
        lc t ->
        Topen_t i (FTName T) (Tclose_t T i t) = t.
    Proof.
      introv Hlc. gen i.
      induction Hlc ; intros ; simpls ; fequals* ;
        try solve [ apply~ Topen_d_Tclose
                  | apply~ Topen_k_Tclose
                  | apply~ Topen_ty_Tclose ].
      - remember (Topen_t i (FTName T) (Tclose_t T i t)).
        pick_fresh x ; substs. applys~ open_inj 0 x.
        rewrite* <- Topen_t_open_comm. rewrite* <- Tclose_t_open_comm. simpls~.
      - remember (Topen_t i (FTName T) (Tclose_t T i t)).
        pick_fresh x ; substs. applys~ topen_t_inj 0 x.
        rewrite* <- Topen_t_topen_comm. rewrite* <- Tclose_t_topen_comm. simpls~.
      - remember (Topen_t i (FTName T) (Tclose_t T i t2)).
        pick_fresh x ; substs. applys~ open_inj 0 x.
        rewrite* <- Topen_t_open_comm. rewrite* <- Tclose_t_open_comm. simpls~.
      - remember (Topen_t (S i) (FTName T) (Tclose_t T (S i) t)).
        pick_fresh X ; substs. applys~ Topen_t_inj 0 X.
        rewrite~ Topen_t_Topen_comm. rewrite~ Topen_t_Tclose_comm.
      - remember (Topen_ty i (FTName T) (Tclose_ty T i ty)).
        pick_fresh X ; substs. applys~ topen_inj 0 X.
        rewrite* <- Topen_ty_topen_comm. rewrite~ <- Tclose_ty_topen_comm ; simpls~.
        apply* Topen_ty_Tclose.
      - solve_var.
      - remember (Topen_t i (FTName T) (Tclose_t T i t)).
        pick_fresh X ; substs. applys~ Kopen_t_inj 0 X.
        rewrite~ Kopen_t_Topen_comm. rewrite~ Kopen_t_Tclose_comm.
      - remember (Topen_t i (FTName T) (Tclose_t T i t)).
        pick_fresh x ; substs. applys~ open_inj 0 x.
        rewrite* <- Topen_t_open_comm. rewrite* <- Tclose_t_open_comm. simpls~.
    Qed.

    Lemma Tclose_d_notin : forall T i d, T \notin Tfv_d (Tclose_d T i d).
    Proof.
      intros. unfolds Tclose_d. unfolds Tfv_d.
      induction d ; rew_listx ; simpls~. destruct a. rewrite notin_union. splits~.
      destruct t ; solve_var.
    Qed.

    Lemma Tclose_k_notin : forall T i k, T \notin Tfv_k (Tclose_k T i k).
    Proof. intros. induction k ; simpls~. apply~ Tclose_d_notin. Qed.

    Lemma Tclose_ty_notin : forall T i ty, T \notin Tfv_ty (Tclose_ty T i ty).
    Proof.
      intros.
      induction ty ; intros ; solve_var ; rewrite_all notin_union ; try split~.
      - apply~ Tclose_k_notin.
      - destruct t ; solve_var.
      - apply~ Tclose_d_notin.
    Qed.

    Lemma Tclose_t_notin : forall T i t, T \notin Tfv_t (Tclose_t T i t).
    Proof.
      intros. gen i.
      induction t ; intros ; solve_var ; rewrite_all notin_union ; repeat split~ ;
        try solve [ apply~ Tclose_d_notin
                  | apply~ Tclose_k_notin
                  | apply~ Tclose_ty_notin ].
      destruct t0 ; solve_var.
    Qed.

    Lemma Kopen_t_open_comm :
      forall i n K v t,
        lc v ->
        Kopen_t i K ([n ~> v] t) = [n ~> v] (Kopen_t i K t).
    Proof.
      introv Hlc. gen n i. solve_eq t. apply* Kopen_t_lc.
    Qed.

    Lemma Kclose_d_fresh :
      forall K i d,
        K \notin Kfv_d d ->
        Kclose_d K i d = d.
    Proof.
      introv Hfv. unfolds Kclose_d. unfolds Kfv_d.
      induction~ d.
      rew_listx in * ; simpls. destruct a. do 2 fequals~.
      induction~ l. rew_listx in * ; simpls. fequals~.
      destruct a ; solve_var.
    Qed.

    Lemma Kclose_k_fresh :
      forall K i k,
        K \notin Kfv_k k ->
        Kclose_k K i k = k.
    Proof. introv Hfv. solve_eq k ; apply~ Kclose_d_fresh. Qed.

    Lemma Kclose_ty_fresh :
      forall K i ty,
        K \notin Kfv_ty ty ->
        Kclose_ty K i ty = ty.
    Proof.
      introv Hfv. solve_eq ty.
      - apply~ Kclose_k_fresh.
      - induction~ l. rew_listx in * ; simpls.
        fequals~. apply~ Kclose_p_fresh.
      - apply~ Kclose_d_fresh.
    Qed.

    Lemma Kclose_t_fresh :
      forall K i t,
        K \notin Kfv_t t ->
        Kclose_t K i t = t.
    Proof.
      introv Hfv. gen i. solve_eq t ;
        try solve [ apply~ Kclose_d_fresh
                  | apply~ Kclose_k_fresh
                  | apply~ Kclose_ty_fresh
                  | apply~ Kclose_p_fresh ].
      destruct c ; solve_var.
    Qed.

    Lemma Kclose_t_open_comm :
      forall i n K v t,
        K \notin Kfv_t v ->
        Kclose_t K i ([n ~> v] t) = [n ~> v] (Kclose_t K i t).
    Proof.
      introv. gen i n. solve_eq t ; apply* Kclose_t_fresh.
    Qed.

    Lemma Kopen_ty_topen_comm :
      forall i n K ty1 ty2,
        lct ty1 ->
        Kopen_ty i K ({n ~> ty1} ty2) = {n ~> ty1} (Kopen_ty i K ty2).
    Proof.
      introv. gen n. solve_eq ty2. apply* Kopen_ty_lct.
    Qed.

    Lemma Kopen_t_topen_comm :
      forall i n K ty t,
        lct ty ->
        Kopen_t i K ([{n ~> ty}] t) = [{n ~> ty}] (Kopen_t i K t).
    Proof.
      introv. gen n i. solve_eq t ; apply* Kopen_ty_topen_comm.
    Qed.

    Lemma Kclose_ty_topen_comm :
      forall i n K ty1 ty2,
        K \notin Kfv_ty ty1 ->
        Kclose_ty K i ({n ~> ty1} ty2) = {n ~> ty1} (Kclose_ty K i ty2).
    Proof.
      introv. gen n. solve_eq ty2 ; apply* Kclose_ty_fresh.
    Qed.

    Lemma Kclose_t_topen_comm :
      forall i n K ty t,
        K \notin Kfv_ty ty ->
        Kclose_t K i ([{n ~> ty}] t) = [{n ~> ty}] (Kclose_t K i t).
    Proof.
      introv. gen n i. solve_eq t ; apply* Kclose_ty_topen_comm.
    Qed.

    Lemma Kopen_d_Kopen_comm :
      forall i j K K' d,
        i <> j ->
        Kopen_d i (FCon K) (Kopen_d j (FCon K') d) =
          Kopen_d j (FCon K') (Kopen_d i (FCon K) d).
    Proof.
      introv Hneq. unfolds Kopen_d.
      induction~ d. destruct a. rew_listx. do 2 fequals~.
      induction~ l. rew_listx. fequals~.
      destruct a ; solve_var.
    Qed.

    Lemma Kopen_k_Kopen_comm :
      forall i j K K' k,
        i <> j ->
        Kopen_k i (FCon K) (Kopen_k j (FCon K') k) =
          Kopen_k j (FCon K') (Kopen_k i (FCon K) k).
    Proof. introv Hneq. solve_eq k ; apply~ Kopen_d_Kopen_comm. Qed.

    Lemma Kopen_ty_Kopen_comm :
      forall i j K K' ty,
        i <> j ->
        Kopen_ty i (FCon K) (Kopen_ty j (FCon K') ty) =
          Kopen_ty j (FCon K') (Kopen_ty i (FCon K) ty).
    Proof.
      introv Hneq. solve_eq ty.
      - apply~ Kopen_k_Kopen_comm.
      - induction~ l. rew_listx. fequals~. apply~ Kopen_p_Kopen_comm.
      - apply~ Kopen_d_Kopen_comm.
    Qed.

    Lemma Kopen_t_Kopen_comm :
      forall i j K K' t,
        i <> j ->
        Kopen_t i (FCon K) (Kopen_t j (FCon K') t) =
          Kopen_t j (FCon K') (Kopen_t i (FCon K) t).
    Proof.
      introv Hneq. gen i j. solve_eq t ;
        try solve [ apply~ Kopen_d_Kopen_comm
                  | apply~ Kopen_k_Kopen_comm
                  | apply~ Kopen_ty_Kopen_comm
                  | apply~ Kopen_p_Kopen_comm ].
      destruct c ; solve_var.
    Qed.

    Lemma Kopen_d_Kclose_comm :
      forall i j K K' d,
        i <> j ->
        K <> K' ->
        Kopen_d i (FCon K) (Kclose_d K' j d) =
          Kclose_d K' j (Kopen_d i (FCon K) d).
    Proof.
      introv Hneq1 Hneq2. unfolds Kopen_d. unfolds Kclose_d.
      induction~ d. destruct a. rew_listx. do 2 fequals~.
      induction~ l. rew_listx. fequals~.
      destruct a ; solve_var.
    Qed.

    Lemma Kopen_k_Kclose_comm :
      forall i j K K' k,
        i <> j ->
        K <> K' ->
        Kopen_k i (FCon K) (Kclose_k K' j k) =
          Kclose_k K' j (Kopen_k i (FCon K) k).
    Proof. intros. solve_eq k ; apply~ Kopen_d_Kclose_comm. Qed.

    Lemma Kopen_ty_Kclose_comm :
      forall i j K K' ty,
        i <> j ->
        K <> K' ->
        Kopen_ty i (FCon K) (Kclose_ty K' j ty) =
          Kclose_ty K' j (Kopen_ty i (FCon K) ty).
    Proof.
      introv Hneq1 Hneq2. solve_eq ty.
      - apply~ Kopen_k_Kclose_comm.
      - induction~ l. rew_listx. fequals~. apply~ Kopen_p_Kclose_comm.
      - apply~ Kopen_d_Kclose_comm.
    Qed.

    Lemma Kopen_t_Kclose_comm :
      forall i j K K' t,
        i <> j ->
        K <> K' ->
        Kopen_t i (FCon K) (Kclose_t K' j t) = Kclose_t K' j (Kopen_t i (FCon K) t).
    Proof.
      introv Hneq1 Hneq2. gen i j. solve_eq t ;
        try solve [ apply~ Kopen_d_Kclose_comm
                  | apply~ Kopen_k_Kclose_comm
                  | apply~ Kopen_ty_Kclose_comm
                  | apply~ Kopen_p_Kclose_comm ].
      destruct c ; solve_var.
    Qed.

    Lemma Kopen_d_Kclose :
      forall i K d,
        lcd d ->
        Kopen_d i (FCon K) (Kclose_d K i d) = d.
    Proof.
      introv Hlc. unfolds lcd. unfolds Kopen_d. unfolds Kclose_d.
      induction~ Hlc. rew_listx. destruct x. do 2 fequals.
      destruct H as (?&HlcK).
      induction~ l0. rew_listx in *. fequals*. destruct HlcK as (HlcK'&?).
      destruct a ; solve_var ; inverts HlcK' ; discriminate.
    Qed.

    Lemma Kopen_k_Kclose :
      forall i K k,
        lck k ->
        Kopen_k i (FCon K) (Kclose_k K i k) = k.
    Proof. introv Hlc. solve_eq Hlc. apply~ Kopen_d_Kclose. Qed.

    Lemma Kopen_ty_Kclose :
      forall i K ty,
        lct ty ->
        Kopen_ty i (FCon K) (Kclose_ty K i ty) = ty.
    Proof.
      introv Hlc. solve_eq Hlc.
      - apply~ Kopen_k_Kclose.
      - remember (Kopen_ty i (FCon K) (Kclose_ty K i T)).
        pick_fresh X ; substs. applys~ topen_inj 0 X.
        rewrite* <- Kopen_ty_topen_comm. rewrite* <- Kclose_ty_topen_comm. simpls~.
      - induction~ ps. rew_listx in *. destruct H. fequals~. apply~ Kopen_p_Kclose.
      - apply~ Kopen_d_Kclose.
    Qed.

    Lemma Topen_d_Kclose_comm :
      forall i j K T d,
        Topen_d i T (Kclose_d K j d) = Kclose_d K j (Topen_d i T d).
    Proof.
      intros. unfolds Kclose_d. unfolds Topen_d.
      induction~ d. destruct a. rew_listx. fequals~.
    Qed.

    Lemma Topen_k_Kclose_comm :
      forall i j K T k,
        Topen_k i T (Kclose_k K j k) = Kclose_k K j (Topen_k i T k).
    Proof. intros. solve_eq k ; apply~ Topen_d_Kclose_comm. Qed.

    Lemma Topen_ty_Kclose_comm :
      forall i j K T ty,
        Topen_ty i T (Kclose_ty K j ty) = Kclose_ty K j (Topen_ty i T ty).
    Proof.
      intros. solve_eq ty.
      - apply~ Topen_k_Kclose_comm.
      - apply~ Topen_d_Kclose_comm.
    Qed.

    Lemma Topen_t_Kclose_comm :
      forall i j K T t,
        Topen_t i T (Kclose_t K j t) = Kclose_t K j (Topen_t i T t).
    Proof.
      intros. gen i j. solve_eq t ;
        try solve [ apply~ Topen_d_Kclose_comm
                  | apply~ Topen_k_Kclose_comm
                  | apply~ Topen_ty_Kclose_comm ].
    Qed.

    Lemma Kopen_t_Kclose :
      forall i K t,
        lc t ->
        Kopen_t i (FCon K) (Kclose_t K i t) = t.
    Proof.
      introv Hlc. gen i.
      induction Hlc ; intros ; simpls ; fequals* ;
        try solve [ apply~ Kopen_d_Kclose
                  | apply~ Kopen_k_Kclose
                  | apply~ Kopen_ty_Kclose
                  | apply~ Kopen_p_Kclose ].
      - remember (Kopen_t i (FCon K) (Kclose_t K i t)).
        pick_fresh x ; substs. applys~ open_inj 0 x.
        rewrite* <- Kopen_t_open_comm. rewrite* <- Kclose_t_open_comm. simpls~.
      - remember (Kopen_t i (FCon K) (Kclose_t K i t)).
        pick_fresh x ; substs. applys~ topen_t_inj 0 x.
        rewrite* <- Kopen_t_topen_comm. rewrite* <- Kclose_t_topen_comm. simpls~.
      - solve_var.
      - remember (Kopen_t i (FCon K) (Kclose_t K i t2)).
        pick_fresh x ; substs. applys~ open_inj 0 x.
        rewrite* <- Kopen_t_open_comm. rewrite* <- Kclose_t_open_comm. simpls~.
      - remember (Kopen_t i (FCon K) (Kclose_t K i t)).
        pick_fresh X ; substs. applys~ Topen_t_inj 0 X.
        rewrite~ <- Kopen_t_Topen_comm. rewrite~ Topen_t_Kclose_comm.
      - remember (Kopen_ty i (FCon K) (Kclose_ty K i ty)).
        pick_fresh X ; substs. applys~ topen_inj 0 X.
        rewrite* <- Kopen_ty_topen_comm. rewrite~ <- Kclose_ty_topen_comm ; simpls~.
        apply* Kopen_ty_Kclose.
      - remember (Kopen_t (S i) (FCon K) (Kclose_t K (S i) t)).
        pick_fresh X ; substs. applys~ Kopen_t_inj 0 X.
        rewrite~ Kopen_t_Kopen_comm. rewrite~ Kopen_t_Kclose_comm.
      - remember (Kopen_t i (FCon K) (Kclose_t K i t)).
        pick_fresh x ; substs. applys~ open_inj 0 x.
        rewrite* <- Kopen_t_open_comm. rewrite* <- Kclose_t_open_comm. simpls~.
    Qed.

    Lemma Kclose_d_notin : forall K i d, K \notin Kfv_d (Kclose_d K i d).
    Proof.
      intros. unfolds Kclose_d. unfolds Kfv_d.
      induction d ; rew_listx ; simpls~. destruct a. rewrite notin_union. splits~.
      induction l ; rew_listx ; simpls~.
      rewrite notin_union. splits~. destruct a ; solve_var.
    Qed.

    Lemma Kclose_k_notin : forall K i k, K \notin Kfv_k (Kclose_k K i k).
    Proof. intros. induction k ; simpls~. apply~ Kclose_d_notin. Qed.

    Lemma Kclose_ty_notin : forall K i ty, K \notin Kfv_ty (Kclose_ty K i ty).
    Proof.
      intros.
      induction ty ; intros ; solve_var ; rewrite_all notin_union ; repeat split~.
      - apply~ Kclose_k_notin.
      - induction l ; rew_listx ; simpls~. rewrite notin_union. split~.
        apply~ Kclose_p_notin.
      - apply~ Kclose_d_notin.
    Qed.

    Lemma Kclose_t_notin : forall K i t, K \notin Kfv_t (Kclose_t K i t).
    Proof.
      intros. gen i.
      induction t ; intros ; solve_var ; rewrite_all notin_union ; repeat split~ ;
        try solve [ apply~ Kclose_d_notin
                  | apply~ Kclose_k_notin
                  | apply~ Kclose_ty_notin
                  | apply~ Kclose_p_notin ].
      destruct c ; solve_var.
    Qed.

    Lemma Tsubst_t_open_distr :
      forall i X T t u,
        Tsubst_t X T ([i ~> u] t) =
          [i ~> Tsubst_t X T u] (Tsubst_t X T t).
    Proof. introv. gen i. solve_eq t. Qed.

    Lemma Tsubst_ty_topen_distr :
      forall i X T ty U,
        Tsubst_ty X T ({i ~> U} ty) =
          {i ~> Tsubst_ty X T U} (Tsubst_ty X T ty).
    Proof. introv. gen i. solve_eq ty. Qed.

    Lemma Tsubst_t_topen_distr :
      forall i X T t U,
        Tsubst_t X T ([{i ~> U}] t) =
          [{i ~> Tsubst_ty X T U}] (Tsubst_t X T t).
    Proof. introv. gen i. solve_eq t ; apply Tsubst_ty_topen_distr. Qed.

    Lemma Tsubst_t_open_comm :
      forall i X T t x,
        Tsubst_t X T ([i ~> TmFVar x] t) = [i ~> TmFVar x] (Tsubst_t X T t).
    Proof. introv. gen i. solve_eq t. Qed.

    Lemma Tsubst_ty_topen_comm :
      forall i X T ty x,
        Tsubst_ty X T ({i ~> TyFVar x} ty) =
          {i ~> TyFVar x} (Tsubst_ty X T ty).
    Proof. introv. gen i. solve_eq ty. Qed.

    Lemma Tsubst_t_topen_comm :
      forall i X T t x,
        Tsubst_t X T ([{i ~> TyFVar x}] t) = [{i ~> TyFVar x}] (Tsubst_t X T t).
    Proof. introv. gen i. solve_eq t ; apply Tsubst_ty_topen_comm. Qed.

    Lemma Tsubst_d_Topen_comm :
      forall i X T U d,
        X <> T ->
        Topen_d i (FTName T) (Tsubst_d X (FTName U) d) =
          Tsubst_d X (FTName U) (Topen_d i (FTName T) d).
    Proof.
      introv Hneq. unfolds Topen_d. unfolds Tsubst_d.
      induction~ d.
      rew_listx in *. destruct a. rewrite~ IHd. destruct t ; solve_var.
    Qed.

    Lemma Tsubst_k_Topen_comm :
      forall i X T U k,
        X <> T ->
        Topen_k i (FTName T) (Tsubst_k X (FTName U) k) =
          Tsubst_k X (FTName U) (Topen_k i (FTName T) k).
    Proof.
      introv Hneq. solve_eq k. apply~ Tsubst_d_Topen_comm.
    Qed.

    Lemma Tsubst_ty_Topen_comm :
      forall i X T U ty,
        X <> T ->
        Topen_ty i (FTName T) (Tsubst_ty X (FTName U) ty) =
          Tsubst_ty X (FTName U) (Topen_ty i (FTName T) ty).
    Proof.
      introv Hneq. solve_eq ty.
      - apply~ Tsubst_k_Topen_comm.
      - destruct t ; solve_var.
      - apply~ Tsubst_d_Topen_comm.
    Qed.

    Lemma Tsubst_t_Topen_comm :
      forall i X T U t,
        X <> T ->
        Topen_t i (FTName T) (Tsubst_t X (FTName U) t) =
          Tsubst_t X (FTName U) (Topen_t i (FTName T) t).
    Proof.
      introv Hneq. gen i. solve_eq t ;
        try solve [ apply~ Tsubst_d_Topen_comm
                  | apply~ Tsubst_k_Topen_comm
                  | apply~ Tsubst_ty_Topen_comm ].
      destruct t0 ; solve_var.
    Qed.

    Lemma Tsubst_d_Kopen_comm :
      forall i X K U d,
        Kopen_d i (FCon K) (Tsubst_d X (FTName U) d) =
          Tsubst_d X (FTName U) (Kopen_d i (FCon K) d).
    Proof.
      intros. unfolds Kopen_d. unfolds Tsubst_d.
      induction~ d.
      rew_listx in *. destruct a. rewrite~ IHd.
    Qed.

    Lemma Tsubst_k_Kopen_comm :
      forall i X K U k,
        Kopen_k i (FCon K) (Tsubst_k X (FTName U) k) =
          Tsubst_k X (FTName U) (Kopen_k i (FCon K) k).
    Proof. intros. solve_eq k. apply~ Tsubst_d_Kopen_comm. Qed.

    Lemma Tsubst_ty_Kopen_comm :
      forall i X K U ty,
        Kopen_ty i (FCon K) (Tsubst_ty X (FTName U) ty) =
          Tsubst_ty X (FTName U) (Kopen_ty i (FCon K) ty).
    Proof.
      intros. solve_eq ty.
      - apply~ Tsubst_k_Kopen_comm.
      - apply~ Tsubst_d_Kopen_comm.
    Qed.

    Lemma Tsubst_t_Kopen_comm :
      forall i X K U t,
        Kopen_t i (FCon K) (Tsubst_t X (FTName U) t) =
          Tsubst_t X (FTName U) (Kopen_t i (FCon K) t).
    Proof.
      introv. gen i. solve_eq t ;
        try solve [ apply~ Tsubst_d_Kopen_comm
                  | apply~ Tsubst_k_Kopen_comm
                  | apply~ Tsubst_ty_Kopen_comm ].
    Qed.

    Lemma Tsubst_d_intro :
      forall X U i d,
        X \notin Tfv_d d ->
        Topen_d i U d = Tsubst_d X U (Topen_d i (FTName X) d).
    Proof.
      introv Hfv. unfolds Topen_d. unfolds Tsubst_d. unfolds Tfv_d.
      induction~ d.
      rew_listx in * ; simpls. destruct a. fequals~. destruct t ; solve_var.
    Qed.

    Lemma Tsubst_k_intro :
      forall X U i k,
        X \notin Tfv_k k ->
        Topen_k i U k = Tsubst_k X U (Topen_k i (FTName X) k).
    Proof. introv Hfv. solve_eq k. apply~ Tsubst_d_intro. Qed.

    Lemma Tsubst_ty_intro :
      forall X U i ty,
        X \notin Tfv_ty ty ->
        Topen_ty i U ty = Tsubst_ty X U (Topen_ty i (FTName X) ty).
    Proof.
      introv Hfv. solve_eq ty.
      - apply~ Tsubst_k_intro.
      - destruct t ; solve_var.
      - apply~ Tsubst_d_intro.
    Qed.

    Lemma Tsubst_t_intro :
      forall X U i t,
        X \notin Tfv_t t ->
        Topen_t i U t = Tsubst_t X U (Topen_t i (FTName X) t).
    Proof.
      introv Hfv. gen i. solve_eq t ;
        try solve [ apply~ Tsubst_d_intro
                  | apply~ Tsubst_k_intro
                  | apply~ Tsubst_ty_intro ].
      destruct t0 ; solve_var.
    Qed.

    Lemma Ksubst_t_open_distr :
      forall i X K t u,
        Ksubst_t X K ([i ~> u] t) =
          [i ~> Ksubst_t X K u] (Ksubst_t X K t).
    Proof. introv. gen i. solve_eq t. Qed.

    Lemma Ksubst_ty_topen_distr :
      forall i X K ty U,
        Ksubst_ty X K ({i ~> U} ty) =
          {i ~> Ksubst_ty X K U} (Ksubst_ty X K ty).
    Proof. introv. gen i. solve_eq ty. Qed.

    Lemma Ksubst_t_topen_distr :
      forall i X K t U,
        Ksubst_t X K ([{i ~> U}] t) =
          [{i ~> Ksubst_ty X K U}] (Ksubst_t X K t).
    Proof. introv. gen i. solve_eq t ; apply Ksubst_ty_topen_distr. Qed.

    Lemma Ksubst_t_open_comm :
      forall i X K t x,
        Ksubst_t X K ([i ~> TmFVar x] t) = [i ~> TmFVar x] (Ksubst_t X K t).
    Proof. introv. gen i. solve_eq t. Qed.

    Lemma Ksubst_ty_topen_comm :
      forall i X K ty x,
        Ksubst_ty X K ({i ~> TyFVar x} ty) =
          {i ~> TyFVar x} (Ksubst_ty X K ty).
    Proof. introv. gen i. solve_eq ty. Qed.

    Lemma Ksubst_t_topen_comm :
      forall i X K t x,
        Ksubst_t X K ([{i ~> TyFVar x}] t) = [{i ~> TyFVar x}] (Ksubst_t X K t).
    Proof. introv. gen i. solve_eq t ; apply Ksubst_ty_topen_comm. Qed.

    Lemma Ksubst_d_Kopen_comm :
      forall i X K U d,
        X <> K ->
        Kopen_d i (FCon K) (Ksubst_d X (FCon U) d) =
          Ksubst_d X (FCon U) (Kopen_d i (FCon K) d).
    Proof.
      introv Hneq. unfolds Kopen_d. unfolds Ksubst_d.
      induction~ d. rew_listx. destruct a. rewrite~ IHd.
      induction~ l. rew_listx. inverts IHl. rewrite H0. destruct a ; solve_var.
    Qed.

    Lemma Ksubst_k_Kopen_comm :
      forall i X K U k,
        X <> K ->
        Kopen_k i (FCon K) (Ksubst_k X (FCon U) k) =
          Ksubst_k X (FCon U) (Kopen_k i (FCon K) k).
    Proof.
      introv Hneq. solve_eq k. apply~ Ksubst_d_Kopen_comm.
    Qed.

    Lemma Ksubst_ty_Kopen_comm :
      forall i X K U ty,
        X <> K ->
        Kopen_ty i (FCon K) (Ksubst_ty X (FCon U) ty) =
          Ksubst_ty X (FCon U) (Kopen_ty i (FCon K) ty).
    Proof.
      introv Hneq. solve_eq ty.
      - apply~ Ksubst_k_Kopen_comm.
      - induction~ l. rew_listx. fequals~. apply~ Ksubst_p_Kopen_comm.
      - apply~ Ksubst_d_Kopen_comm.
    Qed.

    Lemma Ksubst_t_Kopen_comm :
      forall i X K U t,
        X <> K ->
        Kopen_t i (FCon K) (Ksubst_t X (FCon U) t) =
          Ksubst_t X (FCon U) (Kopen_t i (FCon K) t).
    Proof.
      introv Hneq. gen i. solve_eq t ;
        try solve [ apply~ Ksubst_d_Kopen_comm
                  | apply~ Ksubst_k_Kopen_comm
                  | apply~ Ksubst_ty_Kopen_comm
                  | apply~ Ksubst_p_Kopen_comm ].
      destruct c ; solve_var.
    Qed.

    Lemma Ksubst_d_Topen_comm :
      forall i X T U d,
        Topen_d i (FTName T) (Ksubst_d X (FCon U) d) =
          Ksubst_d X (FCon U) (Topen_d i (FTName T) d).
    Proof.
      intros. unfolds Topen_d. unfolds Ksubst_d.
      induction~ d.
      rew_listx in *. destruct a. rewrite~ IHd.
    Qed.

    Lemma Ksubst_k_Topen_comm :
      forall i X T U k,
        Topen_k i (FTName T) (Ksubst_k X (FCon U) k) =
          Ksubst_k X (FCon U) (Topen_k i (FTName T) k).
    Proof. intros. solve_eq k. apply~ Ksubst_d_Topen_comm. Qed.

    Lemma Ksubst_ty_Topen_comm :
      forall i X T U ty,
        Topen_ty i (FTName T) (Ksubst_ty X (FCon U) ty) =
          Ksubst_ty X (FCon U) (Topen_ty i (FTName T) ty).
    Proof.
      intros. solve_eq ty.
      - apply~ Ksubst_k_Topen_comm.
      - apply~ Ksubst_d_Topen_comm.
    Qed.

    Lemma Ksubst_t_Topen_comm :
      forall i X T U t,
        Topen_t i (FTName T) (Ksubst_t X (FCon U) t) =
          Ksubst_t X (FCon U) (Topen_t i (FTName T) t).
    Proof.
      introv. gen i. solve_eq t ;
        try solve [ apply~ Ksubst_d_Topen_comm
                  | apply~ Ksubst_k_Topen_comm
                  | apply~ Ksubst_ty_Topen_comm ].
    Qed.

    Lemma Ksubst_d_intro :
      forall X U i d,
        X \notin Kfv_d d ->
        Kopen_d i U d = Ksubst_d X U (Kopen_d i (FCon X) d).
    Proof.
      introv Hfv. unfolds Kopen_d. unfolds Ksubst_d. unfolds Kfv_d.
      induction~ d. rew_listx in * ; simpls. destruct a. rewrite~ IHd.
      induction~ l. rew_listx in Hfv ; simpls. rew_listx.
      forwards~ IHl': IHl. inverts IHl'.
      rewrite H0. destruct a ; solve_var.
    Qed.

    Lemma Ksubst_k_intro :
      forall X U i k,
        X \notin Kfv_k k ->
        Kopen_k i U k = Ksubst_k X U (Kopen_k i (FCon X) k).
    Proof. introv Hfv. solve_eq k. apply~ Ksubst_d_intro. Qed.

    Lemma Ksubst_ty_intro :
      forall X U i ty,
        X \notin Kfv_ty ty ->
        Kopen_ty i U ty = Ksubst_ty X U (Kopen_ty i (FCon X) ty).
    Proof.
      introv Hfv. solve_eq ty.
      - apply~ Ksubst_k_intro.
      - induction~ l. rew_listx in * ; simpls. fequals~. apply~ Ksubst_p_intro.
      - apply~ Ksubst_d_intro.
    Qed.

    Lemma Ksubst_t_intro :
      forall X U i t,
        X \notin Kfv_t t ->
        Kopen_t i U t = Ksubst_t X U (Kopen_t i (FCon X) t).
    Proof.
      introv Hfv. gen i. solve_eq t ;
        try solve [ apply~ Ksubst_d_intro
                  | apply~ Ksubst_k_intro
                  | apply~ Ksubst_ty_intro
                  | apply~ Ksubst_p_intro ].
      destruct c ; solve_var.
    Qed.

    Lemma Tsubst_d_fresh :
      forall T U d,
        T \notin Tfv_d d ->
        Tsubst_d T U d = d.
    Proof.
      introv Hfv. unfolds. unfolds Tfv_d.
      induction~ d. destruct a.
      rew_listx in * ; simpls. do 2 fequals~. destruct t ; solve_var.
    Qed.

    Lemma Tsubst_k_fresh :
      forall T U k,
        T \notin Tfv_k k ->
        Tsubst_k T U k = k.
    Proof. introv Hfv. solve_eq k. apply~ Tsubst_d_fresh. Qed.

    Lemma Tsubst_ty_fresh :
      forall T U ty,
        T \notin Tfv_ty ty ->
        Tsubst_ty T U ty = ty.
    Proof.
      introv Hfv. solve_eq ty.
      - apply~ Tsubst_k_fresh.
      - destruct t ; solve_var.
      - apply~ Tsubst_d_fresh.
    Qed.

    Lemma Tsubst_t_fresh :
      forall T U t,
        T \notin Tfv_t t ->
        Tsubst_t T U t = t.
    Proof.
      introv Hfv. solve_eq t ;
        try solve [ apply~ Tsubst_d_fresh
                  | apply~ Tsubst_k_fresh
                  | apply~ Tsubst_ty_fresh
                  | apply~ Tsubst_p_fresh ].
      destruct t0 ; solve_var.
    Qed.

    Lemma notin_Topen_d :
      forall i T d,
        T \notin Tfv_d (Topen_d i (FTName T) d) ->
        Topen_d i (FTName T) d = d.
    Proof.
      introv Hfv. unfolds Topen_d. unfolds Tfv_d.
      induction~ d. destruct a.
      rew_listx in * ; simpls. do 2 fequals~. destruct t ; solve_var.
    Qed.

    Lemma notin_Topen_k :
      forall i T k,
        T \notin Tfv_k (Topen_k i (FTName T) k) ->
        Topen_k i (FTName T) k = k.
    Proof.
      introv Hfv. induction k ; simpls ; fequals.
      apply~ notin_Topen_d.
    Qed.

    Lemma notin_Topen_ty :
      forall i T ty,
        T \notin Tfv_ty (Topen_ty i (FTName T) ty) ->
        Topen_ty i (FTName T) ty = ty.
    Proof.
      introv Hfv.
      induction ty ; simpls ; fequals*.
      - apply~ notin_Topen_k.
      - destruct t ; solve_var.
      - apply~ notin_Topen_d.
    Qed.

    Lemma open_notin_T :
      forall i x T t,
        T \notin Tfv_t ([i ~> TmFVar x]t) = T \notin Tfv_t t.
    Proof.
      intros. rew_logic. splits ; gen i.
      { induction t ; introv Hfv ; simpls ; rewrite_all notin_union in Hfv ; solve_var. }
      { induction t ; introv Hfv ; simpls ; solve_var. }
    Qed.

    Lemma topen_notin_T :
      forall T i ty1 ty2,
        T \notin Tfv_ty ty1 ->
        T \notin Tfv_ty ({i ~> ty1}ty2) = T \notin Tfv_ty ty2.
    Proof.
      intros. rew_logic. splits ; gen i.
      { induction ty2 ; introv Hfv ; simpls ; rewrite_all notin_union in Hfv ; solve_var. }
      { induction ty2 ; introv Hfv ; solve_var. }
    Qed.

    Lemma topen_t_notin_T :
      forall i x T t,
        T \notin Tfv_t ([{i ~> TyFVar x}]t) = T \notin Tfv_t t.
    Proof.
      intros. rew_logic. splits ; gen i.
      { induction t ; introv Hfv ; simpls ; rewrite_all notin_union in Hfv ;
          try rewrite topen_notin_T in Hfv; solve_var. }
      { induction t ; introv Hfv ; simpls ; rewrite_all notin_union ; solve_var ;
          try rewrite topen_notin_T ; simpls~. }
    Qed.

    Lemma Topen_d_notin_T :
      forall i x T d,
        T \notin Tfv_d (Topen_d i (FTName x) d) -> T \notin Tfv_d d.
    Proof.
      introv Hnin. unfolds Tfv_d. unfolds Topen_d.
      induction d ; rew_listx in * ; simpls~.
      rewrite notin_union ; split~. destruct a ; destruct t ; solve_var.
    Qed.

    Lemma Topen_k_notin_T :
      forall i x T k,
        T \notin Tfv_k (Topen_k i (FTName x) k) -> T \notin Tfv_k k.
    Proof with eauto using Topen_d_notin_T.
      introv Hnin. induction k; simpls...
    Qed.

    Lemma Topen_ty_notin_T :
      forall i x T ty,
        T \notin Tfv_ty (Topen_ty i (FTName x) ty) -> T \notin Tfv_ty ty.
    Proof with eauto using Topen_k_notin_T, Topen_d_notin_T.
      introv Hnin.
      induction ty; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
      destruct t ; solve_var.
    Qed.

    Lemma Topen_t_notin_T :
      forall i x T t,
        T \notin Tfv_t (Topen_t i (FTName x) t) -> T \notin Tfv_t t.
    Proof with eauto using Topen_ty_notin_T, Topen_k_notin_T, Topen_d_notin_T.
      introv Hnin. gen i.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
      destruct t0 ; solve_var...
    Qed.

    Lemma Kopen_d_notin_T :
      forall i x T d,
        T \notin Tfv_d (Kopen_d i (FCon x) d) -> T \notin Tfv_d d.
    Proof.
      introv Hnin. unfolds Tfv_d. unfolds Kopen_d.
      induction d ; rew_listx in * ; simpls~.
      rewrite notin_union ; split~. destruct a ; destruct t ; solve_var.
    Qed.

    Lemma Kopen_k_notin_T :
      forall i x T k,
        T \notin Tfv_k (Kopen_k i (FCon x) k) -> T \notin Tfv_k k.
    Proof with eauto using Kopen_d_notin_T.
      introv Hnin. induction k; simpls...
    Qed.

    Lemma Kopen_ty_notin_T :
      forall i x T ty,
        T \notin Tfv_ty (Kopen_ty i (FCon x) ty) -> T \notin Tfv_ty ty.
    Proof with eauto using Kopen_k_notin_T, Kopen_d_notin_T.
      introv Hnin.
      induction ty; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma Kopen_t_notin_T :
      forall i x T t,
        T \notin Tfv_t (Kopen_t i (FCon x) t) -> T \notin Tfv_t t.
    Proof with eauto using Kopen_ty_notin_T, Kopen_k_notin_T, Kopen_d_notin_T.
      introv Hnin. gen i.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma Tsubst_inj :
      forall S S' T T',
        T' <> S ->
        T' <> S' ->
        Tsubst T (FTName T') (FTName S) = Tsubst T (FTName T') (FTName S') ->
        S = S'.
    Proof.
      introv Hneq1 Hneq2 Heq.
      solve_var ; inverts~ Heq.
    Qed.

    Lemma Ksubst_d_fresh :
      forall K U d,
        K \notin Kfv_d d ->
        Ksubst_d K U d = d.
    Proof.
      introv Hfv. unfolds. unfolds Kfv_d.
      induction~ d. destruct a.
      rew_listx in * ; simpls. do 2 fequals~.
      induction~ l. rew_listx in * ; simpls. fequals~.
      destruct a ; solve_var.
    Qed.

    Lemma Ksubst_k_fresh :
      forall K U k,
        K \notin Kfv_k k ->
        Ksubst_k K U k = k.
    Proof. introv Hfv. solve_eq k. apply~ Ksubst_d_fresh. Qed.

    Lemma Ksubst_ty_fresh :
      forall K U ty,
        K \notin Kfv_ty ty ->
        Ksubst_ty K U ty = ty.
    Proof.
      introv Hfv. solve_eq ty.
      - apply~ Ksubst_k_fresh.
      - induction~ l. rew_listx in * ; simpls. fequals~. apply~ Ksubst_p_fresh.
      - apply~ Ksubst_d_fresh.
    Qed.

    Lemma Ksubst_t_fresh :
      forall K U t,
        K \notin Kfv_t t ->
        Ksubst_t K U t = t.
    Proof.
      introv Hfv. solve_eq t ;
        try solve [ apply~ Ksubst_d_fresh
                  | apply~ Ksubst_k_fresh
                  | apply~ Ksubst_ty_fresh
                  | apply~ Ksubst_p_fresh ].
      destruct c ; solve_var.
    Qed.

    Lemma notin_Kopen_d :
      forall i K d,
        K \notin Kfv_d (Kopen_d i (FCon K) d) ->
        Kopen_d i (FCon K) d = d.
    Proof.
      introv Hfv. unfolds Kopen_d. unfolds Kfv_d.
      induction~ d. destruct a.
      rew_listx in * ; simpls. do 2 fequals~.
      induction~ l. rew_listx in * ; simpls. fequals~.
      destruct a ; solve_var.
    Qed.

    Lemma notin_Kopen_k :
      forall i K k,
        K \notin Kfv_k (Kopen_k i (FCon K) k) ->
        Kopen_k i (FCon K) k = k.
    Proof.
      introv Hfv. induction k ; simpls ; fequals.
      apply~ notin_Kopen_d.
    Qed.

    Lemma notin_Kopen_ty :
      forall i K ty,
        K \notin Kfv_ty (Kopen_ty i (FCon K) ty) ->
        Kopen_ty i (FCon K) ty = ty.
    Proof.
      introv Hfv.
      induction ty ; simpls ; fequals*.
      - apply~ notin_Kopen_k.
      - induction~ l. rew_listx in * ; simpls. fequals~. apply~ notin_Kopen_p.
      - apply~ notin_Kopen_d.
    Qed.

    Lemma open_notin_K :
      forall i x K t,
        K \notin Kfv_t ([i ~> TmFVar x]t) = K \notin Kfv_t t.
    Proof.
      intros. rew_logic. splits ; gen i.
      { induction t ; introv Hfv ; simpls ; rewrite_all notin_union in Hfv ; solve_var. }
      { induction t ; introv Hfv ; simpls ; solve_var. }
    Qed.

    Lemma topen_notin_K :
      forall K i ty1 ty2,
        K \notin Kfv_ty ty1 ->
        K \notin Kfv_ty ({i ~> ty1}ty2) = K \notin Kfv_ty ty2.
    Proof.
      intros. rew_logic. splits ; gen i.
      { induction ty2 ; introv Hfv ; simpls ; rewrite_all notin_union in Hfv ; solve_var. }
      { induction ty2 ; introv Hfv ; solve_var. }
    Qed.

    Lemma topen_t_notin_K :
      forall i x K t,
        K \notin Kfv_t ([{i ~> TyFVar x}]t) = K \notin Kfv_t t.
    Proof.
      intros. rew_logic. splits ; gen i.
      { induction t ; introv Hfv ; simpls ; rewrite_all notin_union in Hfv ;
          try rewrite topen_notin_K in Hfv; solve_var. }
      { induction t ; introv Hfv ; simpls ; rewrite_all notin_union ; solve_var ;
          try rewrite topen_notin_K ; simpls~. }
    Qed.

    Lemma Kopen_d_notin_K :
      forall i x K d,
        K \notin Kfv_d (Kopen_d i (FCon x) d) -> K \notin Kfv_d d.
    Proof.
      introv Hnin. unfolds Kfv_d. unfolds Kopen_d.
      induction d ; rew_listx in * ; simpls~. destruct a.
      rewrite notin_union ; split~.
      induction l ; rew_listx in * ; simpls~.
      rewrite notin_union ; split~.
      destruct a ; solve_var.
    Qed.

    Lemma Kopen_k_notin_K :
      forall i x K k,
        K \notin Kfv_k (Kopen_k i (FCon x) k) -> K \notin Kfv_k k.
    Proof with eauto using Kopen_d_notin_K.
      introv Hnin. induction k; simpls...
    Qed.

    Lemma Kopen_ty_notin_K :
      forall i x K ty,
        K \notin Kfv_ty (Kopen_ty i (FCon x) ty) -> K \notin Kfv_ty ty.
    Proof with eauto using Kopen_k_notin_K, Kopen_d_notin_K, Kopen_p_notin_K.
      introv Hnin.
      induction ty; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
      rewrite_all notin_union. repeat split...
      induction l ; rew_listx in * ; simpls~.
      rewrite_all notin_union in *. split*. applys* Kopen_p_notin_K.
    Qed.

    Lemma Kopen_t_notin_K :
      forall i x K t,
        K \notin Kfv_t (Kopen_t i (FCon x) t) -> K \notin Kfv_t t.
    Proof with eauto using Kopen_ty_notin_K, Kopen_k_notin_K, Kopen_d_notin_K, Kopen_p_notin_K.
      introv Hnin. gen i.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
      - destruct c ; solve_var...
      - rewrite_all notin_union. repeat split...
    Qed.

    Lemma Topen_d_notin_K :
      forall i x K d,
        K \notin Kfv_d (Topen_d i (FTName x) d) -> K \notin Kfv_d d.
    Proof.
      introv Hnin. unfolds Kfv_d. unfolds Topen_d.
      induction d ; rew_listx in * ; simpls~. destruct a.
      rewrite notin_union ; split~.
    Qed.

    Lemma Topen_k_notin_K :
      forall i x K k,
        K \notin Kfv_k (Topen_k i (FTName x) k) -> K \notin Kfv_k k.
    Proof with eauto using Topen_d_notin_K.
      introv Hnin. induction k; simpls...
    Qed.

    Lemma Topen_ty_notin_K :
      forall i x K ty,
        K \notin Kfv_ty (Topen_ty i (FTName x) ty) -> K \notin Kfv_ty ty.
    Proof with eauto using Topen_k_notin_K, Topen_d_notin_K.
      introv Hnin.
      induction ty; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma Topen_t_notin_K :
      forall i x K t,
        K \notin Kfv_t (Topen_t i (FTName x) t) -> K \notin Kfv_t t.
    Proof with eauto using Topen_ty_notin_K, Topen_k_notin_K, Topen_d_notin_K.
      introv Hnin. gen i.
      induction t; intros; simpls* ; rewrite_all notin_union in Hnin ;
        repeat match goal with | Hand : _ /\ _ |- _ => destruct Hand end...
    Qed.

    Lemma topen_topen_comm :
      forall i j u1 u2 ty,
        i <> j ->
        lct u1 -> lct u2 ->
        {i ~> u1} ({j ~> u2} ty) = {j ~> u2} ({i ~> u1} ty).
    Proof.
      introv Hneq Hlct1 Hlct2. gen i j.
      solve_eq ty ; rewrite~ topen_lct.
    Qed.

    Lemma Ksubst_inj :
      forall S S' K K',
        K' <> S ->
        K' <> S' ->
        Ksubst K (FCon K') (FCon S) = Ksubst K (FCon K') (FCon S') ->
        S = S'.
    Proof.
      introv Hneq1 Hneq2 Heq.
      solve_var ; inverts~ Heq.
    Qed.

  End SyntaxProps1.
End SyntaxProps.
