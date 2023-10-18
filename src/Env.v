From MCore Require Import Syntax Tactics.
From TLC Require Import LibList.
Import LibListNotation.

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
  | SkipTvar  : binding
  | SkipVar   : binding
  .

  Definition env : Type := list binding.

  Definition is_tname (b : binding) : Prop := match b with BindTname => True | _ => False end.
  Definition tnames   (Gamma : env) : env := filter is_tname Gamma.

  Definition is_con (b : binding) : Prop := match b with BindCon _ _ _ => True | _ => False end.
  Definition cons   (Gamma : env) : env := filter is_con Gamma.

  Definition is_tvar (b : binding) : Prop :=
    match b with BindTvar _ => True | SkipTvar => True | _ => False end.
  #[export]
  Hint Unfold is_tvar : mcore.
  Definition tvars   (Gamma : env) : env := filter is_tvar Gamma.

  Definition is_var (b : binding) : Prop :=
    match b with BindVar _ => True | SkipVar => True | _ => False end.
  #[export]
  Hint Unfold is_var : mcore.
  Definition vars   (Gamma : env) : env := filter is_var Gamma.


  Definition is_match (b : binding) : Prop := match b with BindMatch _ => True | _ => False end.
  Definition matches  (Gamma : env) : env := filter is_match Gamma.

  Definition tname_in (T : tname) (Gamma : env) : Prop :=
    Nth T Gamma BindTname.

  Definition con_in (K : con) (d : data) (ty : type) (T : tname) (Gamma : env) : Prop :=
    Nth K Gamma (BindCon d ty T).

  Definition tvar_in (tv : tvar) (k : kind) (Gamma : env) : Prop :=
    Nth tv Gamma (BindTvar k).

  Definition var_in (v : var) (ty : type) (Gamma : env) : Prop :=
    Nth v Gamma (BindVar ty).

  Definition empty_env : env := [ ].


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
        | SkipVar   => b :: vars Gamma
        | _         => vars Gamma
        end.
  Proof. intros ; destruct b ; unfolds ; unfolds is_var ; rew_listx ; case_if*. Qed.

  #[export]
  Hint Rewrite vars_app vars_cons : rew_env.

End Env.
