From Stdlib Require Import String List Bool Arith.
Import ListNotations.

(** Syntax only. No SMT interpretation or State acceptance lives here. *)
Inductive term : Type :=
| Symbol : string -> term
| Apply : term -> term -> term.

Fixpoint term_eqb (x y : term) : bool :=
  match x, y with
  | Symbol a, Symbol b => String.eqb a b
  | Apply f a, Apply g b => if term_eqb f g then term_eqb a b else false
  | _, _ => false
  end.


(* Preserve the original equality definition while allowing the VM to skip the
   argument comparison after an unequal function. This is definitional equality,
   so no extensionality or other axiom is needed. *)
Lemma term_eqb_refinement (x y : term) :
  term_eqb x y =
  (fix eager (left right : term) : bool :=
    match left, right with
    | Symbol a, Symbol b => String.eqb a b
    | Apply f a, Apply g b => eager f g && eager a b
    | _, _ => false
    end) x y.
Proof. reflexivity. Qed.

Inductive pattern : Type :=
| PVar : nat -> pattern
| PNil : string -> pattern
| PSymbol : string -> pattern
| PApply : pattern -> pattern -> pattern.

Inductive expression : Type :=
| ENil : string -> expression -> expression
| EVar : nat -> expression
| ESymbol : string -> expression
| EApply : expression -> expression -> expression
| ENative : string -> list expression -> expression
| ECall : string -> list expression -> expression
| EIf : expression -> expression -> expression -> expression
| EIsOk : expression -> expression
| EIsEq : expression -> expression -> expression
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
  rule_assumption : option pattern;
  rule_premise_list : option string;
  rule_requires : list (expression * expression);
  rule_conclusion : expression
}.
