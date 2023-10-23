From TLC Require Import LibList.
From MCore Require Import Syntax Tactics.

Module Ctx (P : PAT).
  Module S := Syntax P.
  Export S.

  (*****************************)
  (** CONTEXT DEFINITIONS **)
  (*****************************)

  Inductive match_assum : Type :=
  | Match   : term -> pat -> match_assum
  | NoMatch : term -> pat -> match_assum
  .

  Inductive binding : Type :=
  | BindTName : binding
  | BindCon   : data -> type -> tname -> binding
  | BindTVar  : kind -> binding
  | BindVar   : type -> binding
  | BindMatch : match_assum -> binding
  .

  Definition ctx := list binding.

  Definition empty : ctx := nil.

  Definition bsubst (X : var) (U : type) (b : binding) :=
    match b with
    | BindVar T => BindVar (tsubst X U T)
    | BindCon d ty T => BindCon d (tsubst X U ty) T
    | _ => b
    end.

  Definition is_tname (b : binding) : Prop := match b with BindTName => True | _ => False end.
  Definition tnames   (Gamma : ctx) : ctx := filter is_tname Gamma.
  Definition tname_in (T : tname) (Gamma : ctx) : Prop := Nth T (tnames Gamma) BindTName.

  Definition is_con (b : binding) : Prop := match b with BindCon _ _ _ => True | _ => False end.
  Definition cons   (Gamma : ctx) : ctx := filter is_con Gamma.
  Definition con_in (K : con) (d : data) (ty : type) (T : tname) (Gamma : ctx) : Prop :=
    Nth K (cons Gamma) (BindCon d ty T).

  Definition is_tvar (b : binding) : Prop := match b with BindTVar _ => True | _ => False end.
  Definition tvars   (Gamma : ctx) : ctx := filter is_tvar Gamma.
  Definition tvar_in (tv : var) (k : kind) (Gamma : ctx) : Prop :=
    Nth tv (tvars Gamma) (BindTVar k).

  Definition is_var (b : binding) : Prop := match b with BindVar _ => True | _ => False end.
  Definition vars   (Gamma : ctx) : ctx := filter is_var Gamma.
  Definition var_in (v : var) (ty : type) (Gamma : ctx) : Prop :=
    Nth v (vars Gamma) (BindVar ty).

  Definition is_match (b : binding) : Prop := match b with BindMatch _ => True | _ => False end.
  Definition matches  (Gamma : ctx) : ctx := filter is_match Gamma.


  Create HintDb rew_ctx.

  Tactic Notation "rew_ctx" :=
    autorewrite with rew_ctx.
  Tactic Notation "rew_ctx" "~" :=
    rew_ctx; auto_tilde.
  Tactic Notation "rew_ctx" "*" :=
    rew_ctx; auto_star.
  Tactic Notation "rew_ctx" "in" "*" :=
    autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_ctx).
  Tactic Notation "rew_ctx" "~" "in" "*" :=
    rew_ctx in *; auto_tilde.
  Tactic Notation "rew_ctx" "*" "in" "*" :=
    rew_ctx in *; auto_star.
  Tactic Notation "rew_ctx" "in" hyp(H) :=
    autorewrite with rew_ctx in H.
  Tactic Notation "rew_ctx" "~" "in" hyp(H) :=
    rew_ctx in H; auto_tilde.
  Tactic Notation "rew_ctx" "*" "in" hyp(H) :=
    rew_ctx in H; auto_star.

  (* Lemma binds_app_middle_inv : *)
  (*   forall x y1 y2 G1 G2, *)
  (*     binds x y1 (G1 ++ y2 :: G2) -> *)
  (*     x < length G1 /\ binds x y1 (G1 ++ G2) *)
  (*     \/ x = length G1 /\ y1 = y2 *)
  (*     \/ x > length G1 /\ binds (x - 1) y1 (G1 ++ G2). *)
  (* Proof. *)
  (*   introv Hvar. *)
  (*   lets [ in_G1 | (m' & Heqm' & in_G2') ] : Nth_app_inv Hvar. *)
  (*   { left. lets Hlt : Nth_inbound in_G1. nat_comp_to_peano. *)
  (*     split*. apply* Nth_app_l. } *)
  (*   { right. lets [ (Heq0 & Heqty) | (m & Heqm & in_G2) ] : Nth_cons_inv in_G2' ; subst. *)
  (*     { left*. } *)
  (*     { right. split*. simple_math. applys_eq (>> Nth_app_r G1 in_G2). nat_math. } } *)
  (* Qed. *)

  (* Lemma binds_weaken : *)
  (*   forall x y y' G1 G2, *)
  (*     binds x y (G1 ++ G2) -> *)
  (*     x < length G1 /\ binds x y (G1 ++ y' :: G2) *)
  (*     \/ x >= length G1 /\ binds (S x) y (G1 ++ y' :: G2). *)
  (* Proof. *)
  (* Admitted. *)

  (* (* Lemma binds_freshen : *) *)
  (* (*   forall x ty ty' G1 G2, *) *)
  (* (*     binds x (BindVar ty) (G1 ++ G2) -> *) *)
  (* (*     binds x (BindVar (ty)) (G1 ++ G2) -> *) *)
  (* (*     x < length G1 /\ binds x y (G1 ++ y' :: G2) *) *)
  (* (*     \/ x >= length G1 /\ binds (S x) y (G1 ++ y' :: G2). *) *)
  (* (* Proof. *) *)
  (* (* Admitted. *) *)

  Lemma tnames_app : forall G1 G2, tnames (G1 ++ G2) = tnames G1 ++ tnames G2.
  Proof. intros. unfold tnames. rew_listx~. Qed.

  Lemma tnames_cons : forall Gamma b,
      tnames (b :: Gamma) =
        match b with
        | BindTName => b :: tnames Gamma
        | _         => tnames Gamma
        end.
  Proof. intros ; destruct b ; unfolds ; unfolds is_tname ; rew_listx ; case_if*. Qed.

  #[export]
  Hint Rewrite tnames_app tnames_cons : rew_ctx.

  Lemma cons_app : forall G1 G2, cons (G1 ++ G2) = cons G1 ++ cons G2.
  Proof. intros. unfold cons. rew_listx~. Qed.

  Lemma cons_cons : forall Gamma b,
      cons (b :: Gamma) =
        match b with
        | BindCon _ _ _ => b :: cons Gamma
        | _             => cons Gamma
        end.
  Proof. intros ; destruct b ; unfolds ; unfolds is_con ; rew_listx ; case_if*. Qed.

  #[export]
  Hint Rewrite cons_app cons_cons : rew_ctx.

  Lemma tvars_app : forall G1 G2, tvars (G1 ++ G2) = tvars G1 ++ tvars G2.
  Proof. intros. unfold tvars. rew_listx~. Qed.

  Lemma tvars_cons : forall Gamma b,
      tvars (b :: Gamma) =
        match b with
        | BindTVar _ => b :: tvars Gamma
        | _          => tvars Gamma
        end.
  Proof. intros ; destruct b ; unfolds ; unfolds is_tvar ; rew_listx ; case_if*. Qed.

  #[export]
  Hint Rewrite tvars_app tvars_cons : rew_ctx.

  Lemma vars_app : forall G1 G2, vars (G1 ++ G2) = vars G1 ++ vars G2.
  Proof. intros. unfold vars. rew_listx~. Qed.

  Lemma vars_cons : forall Gamma b,
      vars (b :: Gamma) =
        match b with
        | BindVar _ => b :: vars Gamma
        | _         => vars Gamma
        end.
  Proof. intros ; destruct b ; unfolds ; unfolds is_var ; rew_listx ; case_if*. Qed.

  #[export]
  Hint Rewrite vars_app vars_cons : rew_ctx.

End Ctx.
