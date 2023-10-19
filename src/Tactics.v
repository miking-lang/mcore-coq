From TLC Require Import LibLogic LibNat.
From TLC Require Export LibTactics.

Create HintDb mcore.
Ltac auto_star ::= try solve [ auto with mcore
                             | eauto with mcore
                             | intuition eauto with mcore].

Ltac simple_math := nat_comp_to_peano ; repeat (simpls ; case_if ; rew_nat* ; try nat_math).

Ltac magic t := induction t ; intros ; simple_math ; simpls ; fequals*.

(* Rename a hypothesis in scope based on a pattern matching its type. *)
Tactic Notation "with_hyp" open_constr(P) "as" ident(X) :=
  (match goal with | H : P |- _ => let P' := type of H in unify P P'; rename H into X end).


(* Cases, by Aaron Bohannon *)
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Require String. Open Scope string_scope.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "S3Case" constr(name) := Case_aux S3Case name.
