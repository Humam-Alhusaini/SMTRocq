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
  ?is_metadata_literal:(string -> bool) ->
  ?derive_assuming:(string -> term -> term list -> term list -> term option) -> declarations:declaration list -> roots:term list ->
  derive:(string -> term list -> term list -> term option) ->
  Eunoia_frontend.EunoiaProof.proof -> proof
(** Exact declaration types and ordered roots must match the export. Identical
    exported roots retain distinct claims/slots, while the solver assumption
    list is matched against their stable first-occurrence projection.
    Definitions and parallel lets expand using binding IDs. Definitions use
    the private [@t<digits>] namespace; exported/signature names cannot be
    shadowed by definitions or lexical binders. Signature metadata names come
    from CpcGenerated in production. Directives reject. Scoped calls use the
    actual pushed formula and exactly one endpoint. Closed local bindings
    expire, also for caller-constructed parser ASTs. No rule table is built
    here; derivation failure or a differing claimed conclusion rejects. *)
(** Decimal/rational metadata spellings additionally need the explicit
    [is_metadata_literal] callback. Production supplies EoArithmetic.normalize;
    accepting metadata does not authorize reifying a Real object expression.
    The same callback rejects numeric-looking declarations and binders, even
    when their identifiers were quoted. *)
