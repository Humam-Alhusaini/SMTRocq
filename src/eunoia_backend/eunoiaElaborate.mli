(** Untrusted elaboration only. Every command is inspected, including unused
    steps. Final acceptance must rerun derive, syntax binding and semantic gates. *)
type term = Symbol of string | Apply of term * term
val app : string -> term list -> term
val spine : term -> term * term list
val pp_term : Format.formatter -> term -> unit

type declaration = { name : string; typ : term }
type step = {
  id : int;
  name : string;
  rule : string;
  arguments : term list;
  premises : int list;
  premise_terms : term list;
  result : term;
}
type proof = {
  roots : (int * term) list;
  steps : step list;
  capacity : int;
  conflict : int;
}
exception Error of string
val elaborate :
  ?max_expansion:int -> declarations:declaration list -> roots:term list ->
  derive:(string -> term list -> term list -> term option) ->
  Eunoia_frontend.EunoiaProof.proof -> proof
(** Exact declaration types and ordered roots must match the export; definitions
    and parallel lets are expanded with binding IDs. Scopes and directives are
    rejected until their proved checker is integrated. No hard-coded rule table.
    Derivation failure or a differing claimed conclusion rejects the whole file. *)
