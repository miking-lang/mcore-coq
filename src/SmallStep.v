From TLC Require Import LibList LibLN.
From MCore Require Import Syntax SyntaxProps Typing TypingProps.

Module SmallStep (P : PAT).
  Module TP := TypingProps P.
  Export TP.

  Module Type MATCH.
    Parameter match1 : term -> pat -> option term.
    Parameter matchN : term -> list pat -> option (term * nat).
  End MATCH.

  Module SmallStep1 (M : MATCH).
    Export M.

    Inductive is_value : term -> Prop :=
    | VLam   : forall ty t,
        is_value (TmLam ty t)
    | VTyLam : forall k t,
        is_value (TmTyLam k t)
    | VProd : forall v1 v2,
        is_value v1 ->
        is_value v2 ->
        is_value (TmProd v1 v2)
    | VCon : forall K ty v,
        is_value v ->
        is_value (TmCon K ty v)
    | VSem : forall ty p t,
        is_value (TmSem ty p t)
    | VComp : forall v1 v2,
        is_value v1 ->
        is_value v2 ->
        is_value (TmComp v1 v2).
    #[export]
     Hint Constructors is_value : mcore.

    Fixpoint push_value (f : term -> term) (t : term) : term :=
      match t with
      | TmLam ty t' => TmLam ty (f t')
      | TmTyLam k t' => TmTyLam k (f t')
      | TmProd t1 t2 => TmProd (push_value f t1) (push_value f t2)
      | TmCon K ty t' => TmCon K ty (push_value f t')
      | TmSem ty p t' => TmSem ty p (f t')
      | TmComp t1 t2 => TmComp (push_value f t1) (push_value f t2)
      | _ => arbitrary
      end.

    Fixpoint get_cases (t : term) :=
      match t with
      | TmSem ty p t' => (p :: nil , t' :: nil)
      | TmComp t1 t2  =>
          let (ps1 , ts1) := get_cases t1 in
          let (ps2 , ts2) := get_cases t2 in
          (ps1 ++ ps2, ts1 ++ ts2)
      | _ => (nil, nil)
      end.

    Inductive is_context : (term -> term) -> Prop :=
    | CAppL : forall t', is_context (fun t => TmApp t t')
    | CAppR : forall v,
        is_value v ->
        is_context (TmApp v)
    | CTyApp : forall ty, is_context (fun t => TmTyApp t ty)
    | CFix : is_context TmFix
    | CProdL : forall t2, is_context (fun t1 => TmProd t1 t2)
    | CProdR : forall (v : term),
        is_value v ->
        is_context (TmProd v)
    | CProj : forall i, is_context (TmProj i)
    | CCon : forall K ty, is_context (TmCon K ty)
    (* | CMatch : pat -> term -> term -> eval_context *)
    | CCompL : forall t2, is_context (fun t1 => TmComp t1 t2)
    | CCompR : forall (v : term),
        is_value v ->
        is_context (TmComp v)
    | CSemAppL : forall t2, is_context (fun t1 => TmSemApp t1 t2)
    | CSemAppR : forall (v : term),
        is_value v ->
        is_context (TmSemApp v).
    #[export]
     Hint Constructors is_context : mcore.

    Reserved Notation "t1 --> t2" (at level 50).
    Inductive eval_step : term -> term -> Prop :=
    | EApp : forall ty t v,
        is_value v ->
        TmApp (TmLam ty t) v --> [0 ~> v]t
    | ETyApp : forall k t ty,
        TmTyApp (TmTyLam k t) ty --> [{0 ~> ty}]t
    | EFix : forall ty t,
        TmFix (TmLam ty t) --> [0 ~> TmFix (TmLam ty t)]t
    | EProj1 : forall v1 v2,
        is_value v1 ->
        is_value v2 ->
        TmProj F1 (TmProd v1 v2) --> v1
    | EProj2 : forall v1 v2,
        is_value v1 ->
        is_value v2 ->
        TmProj F2 (TmProd v1 v2) --> v2
    | EType : forall v,
        is_value v ->
        TmType v --> push_value TmType v
    | EConDef : forall d ty T v,
        is_value v ->
        TmConDef d ty T v --> push_value (TmConDef d ty T) v
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
    | ESemApp : forall v1 v2 v2' i ps bs,
        is_value v1 ->
        is_value v2 ->
        get_cases v1 = (ps , bs) ->
        matchN v2 ps = Some (v2', i) ->
        TmSemApp v1 v2 --> [0 ~> v2'](nth i bs)
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
    Definition econg_CProdL t2 := ECong (CProdL t2).
    #[export] Hint Resolve econg_CProdL : mcore.
    Definition econg_CProdR v Hv := ECong (CProdR v Hv).
    #[export] Hint Resolve econg_CProdR : mcore.
    Definition econg_CCon K ty := ECong (CCon K ty).
    #[export] Hint Resolve econg_CCon : mcore.
    Definition econg_CCompL t2 := ECong (CCompL t2).
    #[export] Hint Resolve econg_CCompL : mcore.
    Definition econg_CCompR v Hv := ECong (CCompR v Hv).
    #[export] Hint Resolve econg_CCompR : mcore.
    Definition econg_CSemAppL t2 := ECong (CSemAppL t2).
    #[export] Hint Resolve econg_CSemAppL : mcore.
    Definition econg_CSemAppR v Hv := ECong (CSemAppR v Hv).
    #[export] Hint Resolve econg_CSemAppR : mcore.

  End SmallStep1.
End SmallStep.
