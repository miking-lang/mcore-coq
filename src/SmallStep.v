From MCore Require Import Syntax Typing Tactics.

Module SmallStep (P : PAT).
  Module T := Typing P.
  Export T.

  Inductive is_value : term -> Prop :=
  | VLam : forall ty t,
      is_value (TmLam ty t)
  | VTyLam : forall k t,
      is_value (TmTyLam k t)
  (* | VProd : forall {v1 v2 : term}, *)
  (*     is_value v1 -> *)
  (*     is_value v2 -> *)
  (*     is_value (TmProd v1 v2) *)
  | VCon : forall c ty v,
      is_value v ->
      is_value (TmCon c ty v)
  (* | VSem : forall {ty : type} {cases : list (pat * term)}, *)
  (*     is_value (TmSem ty cases) *)
  .
  #[export]
   Hint Constructors is_value : mcore.

  Module Type MATCH.
    Parameter match1 :
      forall {v : term},
        is_value v ->
        pat ->
        option (list term).
    Parameter match_n :
      forall {v : term},
        is_value v ->
        list pat ->
        option (nat * list term).
  End MATCH.

  Module SmallStep (M : MATCH).
    Export M.

    Inductive is_context : (term -> term) -> Type :=
    | CAppL : forall t', is_context (fun t => TmApp t t')
    | CAppR : forall v,
        is_value v ->
        is_context (TmApp v)
    | CTyApp : forall ty, is_context (fun t => TmTyApp t ty)
    (* | CFix : eval_context *)
    (* | CProdL : term -> eval_context *)
    (* | CProdR : forall (v : term), *)
    (*     is_value v -> *)
    (*     eval_context *)
    (* | CProj : fin2 -> eval_context *)
    | CCon : forall K ty, is_context (TmCon K ty)
    (* | CMatch : pat -> term -> term -> eval_context *)
    | CType : is_context TmType
    | CConDef : forall d ty T, is_context (TmConDef d ty T)
    (* | CCompL : term -> eval_context *)
    (* | CCompR : forall (v : term), *)
    (*     is_value v -> *)
    (*     eval_context *)
    (* | CSemAppL : term -> eval_context *)
    (* | CSemAppR : forall (v : term), *)
    (*     is_value v -> *)
    (*     eval_context *)
    .
    #[export]
    Hint Constructors is_context : mcore.

    Reserved Notation "t1 --> t2" (at level 50).
    Inductive eval_step : term -> term -> Prop :=
    | EApp : forall ty t v,
        is_value v ->
        TmApp (TmLam ty t) v --> [0 ~> v]t
    | ETyApp : forall k t ty,
        TmTyApp (TmTyLam k t) ty --> [{0 ~> ty}]t
    (* | EFix : forall {ty : type} {t : term}, *)
    (*     eval_step (TmFix (TmLam ty t)) (tm_subst t (TmFix (TmLam ty t))) *)
    (* | EProj1 : forall {v1 v2 : term}, *)
    (*     is_value v1 -> *)
    (*     is_value v2 -> *)
    (*     eval_step (TmProj F1 (TmProd v1 v2)) v1 *)
    (* | EProj2 : forall {v1 v2 : term}, *)
    (*     is_value v1 -> *)
    (*     is_value v2 -> *)
    (*     eval_step (TmProj F2 (TmProd v1 v2)) v2 *)
    | EType : forall v,
        is_value v ->
        TmType v --> v
    | EConDef : forall d ty T v,
        is_value v ->
        TmConDef d ty T v --> v
    (* | EMatchThen : forall {v t1 t2 : term} {p : pat} *)
    (*                       {theta : list term} *)
    (*                       (vval : is_value v), *)
    (*     match1 vval p = Some theta -> *)
    (*     eval_step (TmMatch v p t1 t2) (tm_subst_n t1 theta) *)
    (* | EMatchElse : forall {v t1 t2 : term} {p : pat} *)
    (*                       (vval : is_value v), *)
    (*     match1 vval p = None -> *)
    (*     eval_step (TmMatch v p t1 t2) t2 *)
    (* | EComp : forall {cases1 cases2 : list (pat * term)} {ty : type}, *)
    (*     eval_step (TmComp (TmSem ty cases1) (TmSem ty cases2)) *)
    (*               (TmSem ty (cases1 ++ cases2)) *)
    (* | ESemApp : forall {v : term} {ty : type} *)
    (*                    {cases : list (pat * term)} *)
    (*                    {i : nat} {theta : list term} *)
    (*                    (vval : is_value v), *)
    (*     match_n vval (map fst cases) = Some (i, theta) -> *)
    (*     eval_step (TmSemApp (TmSem ty cases) v) *)
    (*               (tm_subst_n (nth i (map snd cases)) theta) *)
    | ECong : forall {f : term -> term},
        is_context f ->
        forall t1 t2,
            t1 --> t2   ->
          f t1 --> f t2
    where "t1 --> t2" := (eval_step t1 t2).
    #[export]
    Hint Constructors eval_step : mcore.

    Definition econg_CAppL t2 := ECong (CAppL t2).
    #[export] Hint Resolve econg_CAppL : mcore.
    Definition econg_CAppR v Hv := ECong (CAppR v Hv).
    #[export] Hint Resolve econg_CAppR : mcore.
    Definition econg_CTyApp ty := ECong (CTyApp ty).
    #[export] Hint Resolve econg_CTyApp : mcore.
    Definition econg_CCon K ty := ECong (CCon K ty).
    #[export] Hint Resolve econg_CCon : mcore.
    Definition econg_CType := ECong CType.
    #[export] Hint Resolve econg_CType : mcore.
    Definition econg_CConDef d ty T := ECong (CConDef d ty T).
    #[export] Hint Resolve econg_CConDef : mcore.

    Lemma Topen_value : forall i T t, is_value (Topen_t i T t) -> is_value t.
    Proof. introv Hv. induction t ; inverts* Hv. Qed.

    Lemma value_Topen : forall i T t, is_value t -> is_value (Topen_t i T t).
    Proof. introv Hv. induction t ; inverts* Hv. Qed.

    Lemma Topen_step :
      forall i T t1 t2,
        Topen_t i T t1 --> t2 ->
        exists t2', t1 --> t2'.
    Proof. Admitted.
      (* introv Hstep. *)
      (* induction t1. *)
      (* - inverts Hstep. *)
      (*   with_hyp (is_context _) as ctx. with_hyp (_ = _) as eq. inverts ctx ; inverts eq. *)
      (* - inverts Hstep. *)
      (*   with_hyp (is_context _) as ctx. with_hyp (_ = _) as eq. inverts ctx ; inverts eq. *)
      (* - inverts Hstep. *)
      (*   with_hyp (is_context _) as ctx. with_hyp (_ = _) as eq. inverts ctx ; inverts eq. *)
      (* - simpls. inverts Hstep. *)
      (*   + substs H *)

    Lemma step_Topen :
      forall i T t1 t2,
        t1 --> t2 ->
        Topen_t i T t1 --> Topen_t i T t2.
    Admitted.

    Lemma Kopen_value : forall i K t, is_value (Kopen_t i K t) -> is_value t.
    Proof. introv Hv. induction t ; inverts* Hv. Qed.

    Lemma value_Kopen : forall i K t, is_value t -> is_value (Kopen_t i K t).
    Proof. introv Hv. induction t ; inverts* Hv. Qed.

    Lemma Kopen_step :
      forall i K t1 t2,
        Kopen_t i K t1 --> t2 ->
        exists t2', t1 --> t2'.
    Proof. Admitted.

    Lemma step_Kopen :
      forall i K t1 t2,
        t1 --> t2 ->
        Kopen_t i K t1 --> Kopen_t i K t2.
    Admitted.

  End SmallStep.
End SmallStep.
