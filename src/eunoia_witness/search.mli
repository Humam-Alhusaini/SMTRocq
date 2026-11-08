(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

open Common.SmtAtom

type limits = {
  max_clauses : int;
  max_resolution_pairs : int;
  max_boolean_pairs : int; (** Early Boolean resolution prefix; zero disables it. *)
  max_theory_rounds : int;
  max_terms : int;
  max_formulas : int;
  max_lia_literals : int;
}
val default_limits : limits

type failure = Invalid_input of string | Resource_limit of string | Unsupported
val string_of_failure : failure -> string

(** Per-inference proof search only. Inputs must be canonical and belong to the
    supplied tables. Intermediate equalities may be interned into those tables.
    [Ok] is an untrusted candidate, never a semantic acceptance decision. *)
val produce :
  ?limits:limits -> atoms:Atom.reify_tbl -> forms:Form.reify ->
  premises:Form.t list list -> conclusion:Form.t list -> unit ->
  (Certificate.witness, failure) result

(** Bounded direct-clause search for [EunoiaLocalDirect.gate]. Roots are
    exactly [premises]; the final slot contains [conclusion]. A caller can
    fall back to [produce] on failure. No candidate is accepted natively. *)
val produce_derivation :
  ?limits:limits -> atoms:Atom.reify_tbl -> forms:Form.reify ->
  premises:Form.t list list -> conclusion:Form.t list -> unit ->
  (Certificate.witness, failure) result
