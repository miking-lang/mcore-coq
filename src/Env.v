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
  | BindVar   : option type -> binding
  | BindMatch : match_assum -> binding
  .

  Definition env : Type := list binding.

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

  Definition tname_in (T : tname) (Gamma : env) : Prop :=
    Nth T Gamma BindTname.

  Definition con_in (K : con) (d : data) (ty : type) (T : tname) (Gamma : env) : Prop :=
    Nth K Gamma (BindCon d ty T).

  Definition tvar_in (tv : tvar) (k : kind) (Gamma : env) : Prop :=
    Nth tv Gamma (BindTvar k).

  Definition var_in (v : var) (ty : option type) (Gamma : env) : Prop :=
    Nth v Gamma (BindVar ty).

  Definition empty_env : env := [ ].



  Lemma vars_app : forall G1 G2, vars (G1 ++ G2) = vars G1 ++ vars G2.
  Proof. intros. unfold vars. rew_listx~. Qed.

  Lemma vars_cons : forall Gamma b,
      vars (b :: Gamma) =
        match b with
        | BindVar _ => b :: vars Gamma
        | _         => vars Gamma
        end.
  Proof. intros ; destruct b ; unfold vars ; rew_listx ; rew_mcore~. Qed.

  #[export]
  Hint Rewrite vars_app vars_cons : rew_mcore.

  (* Lemma var_in_n : forall G1 G2 b, *)
  (*     var_in (length G1) (G1 ++ b ++ G2) = *)
  (*       match b with *)
  (*       | BindVar _ => b :: vars Gamma *)
  (*       | _         => vars Gamma *)
  (*       end. *)
  (* Proof. intros ; destruct b ; unfold vars ; rew_listx ; rew_mcore~. Qed. *)

End Env.
