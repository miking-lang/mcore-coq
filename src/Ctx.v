From TLC Require Import LibList.
From MCore Require Import Syntax Tactics.

Module Ctx (P : PAT).
  Module S := Syntax P.
  Export S.

  (*************************)
  (** CONTEXT DEFINITIONS **)
  (*************************)

  Inductive match_assum : Type :=
  | Match   : term -> pat -> match_assum
  | NoMatch : term -> pat -> match_assum
  .

  Inductive binding : Type :=
  | BindTName : binding
  | BindCon   : data -> type -> tname -> binding
  | BindTVar  : kind -> binding
  | BindVar   : type -> binding
  (* | BindMatch : match_assum -> binding *)
  | Skip      : binding
  .

  Definition ctx := list binding.

  Definition empty : ctx := nil.

  Definition bsubst (X : var) (U : type) (b : binding) :=
    match b with
    | BindVar T => BindVar (tsubst X U T)
    | BindCon d ty T => BindCon d (tsubst X U ty) T
    | _ => b
    end.

  Definition in_ctx (x : var) (b : binding) (Gamma : ctx) : Prop := Nth x Gamma b.

  Inductive refines : ctx -> ctx -> Prop :=
  | RefRefl  : forall G1, refines G1 G1
  | RefTrans : forall G1 G2 G3, refines G1 G2 -> refines G2 G3 -> refines G1 G3
  | RefSkip  : forall G1 G2, refines (G1 ++ G2) (G1 & Skip ++ G2)
  .
  #[export]
   Hint Constructors refines : mcore.

End Ctx.
