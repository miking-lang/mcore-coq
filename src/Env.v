From MCore Require Import Syntax Tactics.
From TLC Require Import LibNat LibList.

Open Scope nat_scope.

Module Env (P : PAT).
  Module S := Syntax P.
  Export S.

  Inductive match_assum : Type :=
  | Match   : term -> pat -> match_assum
  | NoMatch : term -> pat -> match_assum
  .

  Inductive binding : Type :=
  | BindTname : binding
  | BindCon   : data -> type -> tname -> binding
  | BindTvar  : kind -> binding
  | BindVar   : type -> binding
  | BindMatch : match_assum -> binding
  .

  Definition env : Type := list binding.

  Definition empty_env : env := nil.

  Definition is_tname (b : binding) : Prop := match b with BindTname => True | _ => False end.
  Definition tnames   (Gamma : env) : env := filter is_tname Gamma.

  Definition is_con (b : binding) : Prop := match b with BindCon _ _ _ => True | _ => False end.
  Definition cons   (Gamma : env) : env := filter is_con Gamma.

  Definition is_tvar (b : binding) : Prop := match b with BindTvar _ => True | _ => False end.
  Definition tvars   (Gamma : env) : env := filter is_tvar Gamma.

  Definition is_var (b : binding) : Prop := match b with BindVar _ => True | _ => False end.
  Definition vars   (Gamma : env) : env := filter is_var Gamma.

  Definition is_match (b : binding) : Prop := match b with BindMatch _ => True | _ => False end.
  Definition matches  (Gamma : env) : env := filter is_match Gamma.

  Definition binds (n : nat) (b : binding) (Gamma : env) : Prop := Nth n Gamma b.

  Definition tname_in (T : tname) (Gamma : env) : Prop :=
    binds T BindTname (tnames Gamma).

  Definition con_in (K : con) (d : data) (ty : type) (T : tname) (Gamma : env) : Prop :=
    binds K (BindCon d ty T) (cons Gamma).

  Definition tvar_in (tv : tvar) (k : kind) (Gamma : env) : Prop :=
    binds tv (BindTvar k) (tvars Gamma).

  Definition var_in (v : var) (ty : type) (Gamma : env) : Prop :=
    binds v (BindVar ty) (vars Gamma).


  Create HintDb rew_env.

  Tactic Notation "rew_env" :=
    autorewrite with rew_env.
  Tactic Notation "rew_env" "~" :=
    rew_env; auto_tilde.
  Tactic Notation "rew_env" "*" :=
    rew_env; auto_star.
  Tactic Notation "rew_env" "in" "*" :=
    autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_env).
  Tactic Notation "rew_env" "~" "in" "*" :=
    rew_env in *; auto_tilde.
  Tactic Notation "rew_env" "*" "in" "*" :=
    rew_env in *; auto_star.
  Tactic Notation "rew_env" "in" hyp(H) :=
    autorewrite with rew_env in H.
  Tactic Notation "rew_env" "~" "in" hyp(H) :=
    rew_env in H; auto_tilde.
  Tactic Notation "rew_env" "*" "in" hyp(H) :=
    rew_env in H; auto_star.


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
  Hint Rewrite vars_app vars_cons : rew_env.

  Lemma binds_app_middle_inv :
    forall x y1 y2 G1 G2,
      binds x y1 (G1 ++ y2 :: G2) ->
      x < length G1 /\ binds x y1 (G1 ++ G2)
      \/ x = length G1 /\ y1 = y2
      \/ x > length G1 /\ binds (x - 1) y1 (G1 ++ G2).
  Proof.
    introv Hvar.
    lets [ in_G1 | (m' & Heqm' & in_G2') ] : Nth_app_inv Hvar.
    { left. lets Hlt : Nth_inbound in_G1. nat_comp_to_peano.
      split*. apply* Nth_app_l. }
    { right. lets [ (Heq0 & Heqty) | (m & Heqm & in_G2) ] : Nth_cons_inv in_G2' ; subst.
      { left*. }
      { right. split*. simple_math. applys_eq (>> Nth_app_r G1 in_G2). nat_math. } }
  Qed.

End Env.
