From Stdlib Require Import String List Bool.
From SMTCoq.checker.eunoia Require Import EoSyntax.
Import ListNotations.
Open Scope string_scope.

(** Syntax ordering for signature polynomial canonicalization only. Ethos
    f97393ea55f03653689e104d0e9c9010ee17780c compares unique first-use IDs,
    not numeric values or SMT semantics. See tools/eunoia/LIA-VALIDATION.md
    for the replacement-order invariant and its limits. *)
Module EoOrder.
Fixpoint compare (x y : term) : comparison :=
  match x, y with
  | Symbol a, Symbol b => String.compare a b
  | Symbol _, Apply _ _ => Lt
  | Apply _ _, Symbol _ => Gt
  | Apply f a, Apply g b =>
      match compare f g with Eq => compare a b | c => c end
  end.
Definition eval (args : list term) : option term :=
  match args with
  | [x; y] => Some (Symbol (match compare x y with Gt => "true" | _ => "false" end))
  | _ => None
  end.
End EoOrder.
