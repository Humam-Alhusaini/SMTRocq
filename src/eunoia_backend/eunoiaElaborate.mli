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
type trace = Done | Next of step * trace
  | Push of int * term * trace * step * trace
(** Push slot, actual assumption, body, discharge (one exact endpoint), rest.
    Slot allocation is globally fresh; only the discharge survives in parent. *)
type proof = {
  roots : (int * term) list;
  steps : step list;
  trace : trace;
  capacity : int;
  conflict : int;
}
exception Error of string
val elaborate :
  ?max_expansion:int -> ?signature_names:string list ->
  ?derive_assuming:(string -> term -> term list -> term list -> term option) -> declarations:declaration list -> roots:term list ->
  derive:(string -> term list -> term list -> term option) ->
  Eunoia_frontend.EunoiaProof.proof -> proof
(** Exact declaration types and ordered roots must match the export; definitions
    and parallel lets are expanded with binding IDs. Definitions must use the
    pinned printer's private [@t<digits>] namespace to prevent signature shadowing. Signature names come from generated Rocq metadata in production. Directives
    reject. Scoped calls use the actual pushed formula and exactly one endpoint;
    closed local bindings expire even for caller-constructed parser ASTs. No hard-coded rule table.
    Derivation failure or a differing claimed conclusion rejects the whole file. *)
