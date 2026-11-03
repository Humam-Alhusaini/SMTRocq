From Stdlib Require Import String List Bool Arith.
Import ListNotations.

(** Syntax only. No SMT interpretation or State acceptance lives here. *)
Inductive term : Type :=
| Symbol : string -> term
| Apply : term -> term -> term.

Fixpoint term_eqb (x y : term) : bool :=
  match x, y with
  | Symbol a, Symbol b => String.eqb a b
  | Apply f a, Apply g b => term_eqb f g && term_eqb a b
  | _, _ => false
  end.

Inductive pattern : Type :=
| PVar : nat -> pattern
| PSymbol : string -> pattern
| PApply : pattern -> pattern -> pattern.

Inductive expression : Type :=
| EVar : nat -> expression
| ESymbol : string -> expression
| EApply : expression -> expression -> expression
| ECall : string -> list expression -> expression
| EIf : expression -> expression -> expression -> expression
| EEq : expression -> expression -> expression
| ERequires : expression -> expression -> expression -> expression
| ETypeof : expression -> expression
| ELet : nat -> expression -> expression -> expression.

Definition bindings := list (nat * term).
Definition binder_types := list (nat * pattern).

Record program_case := {
  case_patterns : list pattern;
  case_body : expression
}.

Record program := {
  program_binders : binder_types;
  program_inputs : list pattern;
  program_output : pattern;
  program_cases : list program_case
}.

Record rule := {
  rule_binders : binder_types;
  rule_arguments : list pattern;
  rule_premises : list pattern;
  rule_requires : list (expression * expression);
  rule_conclusion : expression
}.
