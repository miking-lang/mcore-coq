From MCore Require Import Syntax.
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
  | BTname : binding
  | Bcon   : data -> type -> tname -> binding
  | Btvar  : kind -> binding
  | Bvar   : type -> binding
  | Bmatch : match_assum -> binding
  .

  Definition env : Type := list binding.

  Definition is_tname (b : binding) : Prop := match b with BTname => True | _ => False end.
  Definition tnames   (Gamma : env) : env := filter is_tname Gamma.

  Definition is_con (b : binding) : Prop := match b with Bcon _ _ _ => True | _ => False end.
  Definition cons   (Gamma : env) : env := filter is_con Gamma.

  Definition is_tvar (b : binding) : Prop := match b with Btvar _ => True | _ => False end.
  Definition tvars   (Gamma : env) : env := filter is_tvar Gamma.

  Definition is_var (b : binding) : Prop := match b with Bvar _ => True | _ => False end.
  Definition vars   (Gamma : env) : env := filter is_var Gamma.

  Definition is_match (b : binding) : Prop := match b with Bmatch _ => True | _ => False end.
  Definition matches (Gamma : env) : env := filter is_match Gamma.

  Definition tname_in (T : tname) (Gamma : env) : Prop :=
    Nth T Gamma BTname.

  Definition con_in (K : con) (d : data) (ty : type) (T : tname) (Gamma : env) : Prop :=
    Nth K Gamma (Bcon d ty T).

  Definition tvar_in (tv : tvar) (k : kind) (Gamma : env) : Prop :=
    Nth tv Gamma (Btvar k).

  Definition var_in (v : var) (ty : type) (Gamma : env) : Prop :=
    Nth v Gamma (Bvar ty).

  Definition empty_env : env := [ ].
End Env.
