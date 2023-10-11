From MCore Require Import Syntax Typing Tactics.
From TLC Require Import LibList.

Module SmallStep (P : PAT).
  Module T := Typing P.
  Export T.

  Inductive is_value : term -> Prop :=
  | VLam : forall {ty : type} {t : term},
      is_value (TmLam ty t)
  | VTyLam : forall {k : kind} {t : term},
      is_value (TmTyLam k t)
  (* | VProd : forall {v1 v2 : term}, *)
  (*     is_value v1 -> *)
  (*     is_value v2 -> *)
  (*     is_value (TmProd v1 v2) *)
  (* | VCon : forall {c : con} {ty : type} {v : term}, *)
  (*     is_value v -> *)
  (*     is_value (TmCon c ty v) *)
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
    | CAppL : forall (t' : term), is_context (fun t => TmApp t t')
    | CAppR : forall (v : term),
        is_value v ->
        is_context (TmApp v)
    | CTyApp : forall (ty : type), is_context (fun t => TmTyApp t ty)
    (* | CFix : eval_context *)
    (* | CProdL : term -> eval_context *)
    (* | CProdR : forall (v : term), *)
    (*     is_value v -> *)
    (*     eval_context *)
    (* | CProj : fin2 -> eval_context *)
    (* | CCon : con -> type -> eval_context *)
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

    Inductive eval_step : term -> term -> Prop :=
    | EApp : forall {ty : type} {t v : term},
        is_value v ->
        eval_step (TmApp (TmLam ty t) v) (tm_subst t v)
    | ETyApp : forall {k : kind} {t : term} {ty : type},
        eval_step (TmTyApp (TmTyLam k t) ty) (tm_ty_subst t ty)
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
    (* | EMatchThen : forall {v t1 t2 : term} {p : pat} *)
    (*                       {theta : list term} *)
    (*                       (vval : is_value v), *)
    (*     match1 vval p = Some theta -> *)
    (*     eval_step (TmMatch v p t1 t2) (tm_subst_n t1 theta) *)
    (* | EMatchElse : forall {v t1 t2 : term} {p : pat} *)
    (*                       (vval : is_value v), *)
    (*     match1 vval p = None -> *)
    (*     eval_step (TmMatch v p t1 t2) t2 *)
    (* | EType : forall {t : term}, *)
    (*     eval_step (TmType t) t *)
    (* | EConDef : forall {d : data} {ty : type} {T : tname} {t : term}, *)
    (*     eval_step (TmConDef d ty T t) t *)
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
          eval_step t1 t2 ->
          eval_step (f t1) (f t2)
    .
    #[export]
    Hint Constructors eval_step : mcore.

    Definition econg_CAppL t2 := ECong (CAppL t2).
    #[export] Hint Resolve econg_CAppL : mcore.
    Definition econg_CAppR v Hv := ECong (CAppR v Hv).
    #[export] Hint Resolve econg_CAppR : mcore.
    Definition econg_CTyApp ty := ECong (CTyApp ty).
    #[export] Hint Resolve econg_CTyApp : mcore.
  End SmallStep.
End SmallStep.
