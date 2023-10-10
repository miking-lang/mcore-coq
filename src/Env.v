From MCore Require Import Syntax.
From TLC Require Import LibList.
From RecordUpdate Require Import RecordSet.
Import LibListNotation.

Module Env (P : PAT).
  Module S := Syntax P.
  Export S.

  Inductive match_assum : Type :=
  | Match   : term -> pat -> match_assum
  | NoMatch : term -> pat -> match_assum
  .

  Definition tname_env := nat.
  Definition con_env   := list (data * type * tname).
  Definition tvar_env  := list kind.
  Definition var_env   := list type.
  Definition match_env := list match_assum.

  Record env : Type :=
    { tnames  : tname_env
    ; cons    : con_env
    ; tvars   : tvar_env
    ; vars    : var_env
    ; matches : match_env
    }
  .

  #[export]
   Instance eta_env : Settable _ := settable! Build_env <tnames; cons; tvars; vars; matches>.

  Definition tname_in (T : tname) (env : tname_env) : Prop :=
    T < env.

  Definition con_in (K : con) (d : data) (ty : type) (T : tname) (env : con_env) : Prop :=
    Nth K env (d, ty, T).

  Definition tvar_in (tv : tvar) (k : kind) (env : tvar_env) : Prop :=
    Nth tv env k.

  Definition var_in (v : var) (ty : type) (env : var_env) : Prop :=
    Nth v env ty.

  Definition empty_env : env :=
    {| tnames := 0
    ; cons    := [ ]
    ; tvars   := [ ]
    ; vars    := [ ]
    ; matches := [ ]
    |}.
End Env.
