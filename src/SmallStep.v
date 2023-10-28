From TLC Require Import LibLN.
From MCore Require Import Syntax Typing Tactics.

Module SmallStep (P : PAT).
  Module T := Typing P.
  Export T.

  Inductive is_value : term -> Prop :=
  | VLam   : forall ty t,
      is_value (TmLam ty t)
  | VTyLam : forall k t,
      is_value (TmTyLam k t)
  (* | VProd : forall {v1 v2 : term}, *)
  (*     is_value v1 -> *)
  (*     is_value v2 -> *)
  (*     is_value (TmProd v1 v2) *)
  | VCon : forall K ty v,
      is_value v ->
      is_value (TmCon K ty v)
  (* | VSem : forall {ty : type} {cases : list (pat * term)}, *)
  (*     is_value (TmSem ty cases) *)
  .
  #[export]
   Hint Constructors is_value : mcore.

  Inductive push_value : (term -> term) -> term -> term -> Prop :=
  | PLam   : forall ty t f,
      push_value f (TmLam ty t) (TmLam ty (f t))
  | PTyLam : forall k t f,
      push_value f (TmTyLam k t) (TmTyLam k (f t))
  | PCon   : forall K ty t t' f,
      push_value f t t' ->
      push_value f (TmCon K ty t) (TmCon K ty t')
  .
  #[export]
   Hint Constructors push_value : mcore.

  Module Type MATCH.
    Parameter match1 :
      forall v,
        is_value v ->
        pat ->
        option (list term).
    Parameter match_n :
      forall v,
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
    | EType : forall v v',
        is_value v ->
        push_value TmType v v' ->
        TmType v --> v'
    | EConDef : forall d ty T v v',
        is_value v ->
        push_value (TmConDef d ty T) v v' ->
        TmConDef d ty T v --> v'
    | ETypeCong : forall L t1 t2,
        (forall T, T \notin L ->
              Topen_t 0 (FTName T) t1 --> Topen_t 0 (FTName T) t2) ->
        TmType t1 --> TmType t2
    | EConDefCong : forall L d ty T t1 t2,
        (forall K, K \notin L ->
              Kopen_t 0 (FCon K) t1 --> Kopen_t 0 (FCon K) t2) ->
        TmConDef d ty T t1 --> TmConDef d ty T t2
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
    | ECong : forall {f},
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

    Lemma is_value_push : forall f v, is_value v -> exists v', push_value f v v'.
    Proof. introv Hval. induction* Hval. destruct* IHHval. Qed.

    Lemma Topen_is_value :
      forall i T v,
        is_value (Topen_t i T v) ->
        is_value v.
    Proof.
      introv Hval.
      induction v ; inverts* Hval.
    Qed.

    Lemma Topen_step_change :
      forall i T T' t1 t2,
        Topen_t i T t1 --> Topen_t i T t2 ->
        Topen_t i T' t1 --> Topen_t i T' t2.
    Admitted.

    Lemma Kopen_is_value :
      forall i K v,
        is_value (Kopen_t i K v) ->
        is_value v.
    Proof.
      introv Hval.
      induction v ; inverts* Hval.
    Qed.

    Lemma Kopen_step_change :
      forall i K K' t1 t2,
        Kopen_t i K t1 --> Kopen_t i K t2 ->
        Kopen_t i K' t1 --> Kopen_t i K' t2.
    Admitted.

  End SmallStep.
End SmallStep.
