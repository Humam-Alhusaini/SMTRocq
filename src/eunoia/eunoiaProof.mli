(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(** Untrusted, signature-independent reader for a strict CPC text subset.

    [Ok proof] means only that text, command structure and named references
    were read. It is never evidence that a proof is valid. Integration must
    elaborate every term/rule using the generated signature, bind every root
    assumption to the input, check every step and claimed conclusion, implement
    scope discharge, and require a checked refutation. No command is discarded. *)

type position = { offset : int; line : int; column : int }
(** Byte offsets, with one-based lines and columns. *)
type span = { start : position; stop : position }
type diagnostic = { source : string; span : span; message : string }
val pp_diagnostic : Format.formatter -> diagnostic -> unit

type symbol = { text : string; quoted : bool; loc : span }
(** Quoting is retained, but name identity is [text]: [x] and [|x|] collide. *)

type literal =
  | Numeral of string
  | Decimal of string
  | Rational of string
  | Binary of string
  | Hexadecimal of string
  | String of string
(** Numeric spellings are exact. String contents exclude delimiters, retain
    doubled quotes and backslashes exactly, and are NOT unicode-decoded.
    In particular SMT-LIB [\u] escapes belong to later term elaboration. *)

type binding_id = int
type proof_id = int
type scope_id = int
(** IDs are unique within one parsed input; they are not CPC numeric suffixes,
    checker state slots, or offsets from the top of a proof stack. *)

type term = { loc : span; view : term_view }
and term_view =
  | Name of symbol * binding_id option
  | Literal of literal
  | Apply of term * term list
  | Let of let_binding list * term
and let_binding = { binding : binding_id; name : symbol; value : term }
(** [Name (_, Some id)] refers to a preceding in-scope declaration/definition
    or a lexical binder. [None] is unresolved signature syntax, never an implicit
    declaration. Elaboration must reject unresolved unknown symbols. Parallel
    [let] values are read in the outer environment. No macro is expanded. *)

type parameter = { binding : binding_id; name : symbol; sort : term }
type declaration_kind =
  | Sort of int
  | Const of term
  | Fun of term list * term
type declaration = {
  binding : binding_id;
  name : symbol;
  scope : scope_id option;
  kind : declaration_kind;
}
type definition = {
  binding : binding_id;
  name : symbol;
  scope : scope_id option;
  parameters : parameter list;
  body : term;
}
type assumption = {
  id : proof_id;
  name : symbol;
  scope : scope_id option;
  formula : term;
}
type premise = { name : symbol; target : proof_id }
(** Every premise resolves to a preceding, still-visible assumption or step. *)
type step = {
  id : proof_id;
  name : symbol;
  scope : scope_id option;
  rule : symbol;
  args : term list;
  premises : premise list;
  conclusion : term option;
}
(** Rule names, argument order, premise order/multiplicity, and optional claimed
    conclusions are preserved. Rules (including [trust]) are uninterpreted. *)

type directive = Include of string | Reference of string
(** Paths retain their exact string contents. No file is opened by a directive.
    Normalizing reference routines and escaped paths are unsupported. *)
type command_view =
  | Declare of declaration
  | Define of definition
  | Assume of assumption
  | Assume_push of scope_id * assumption
  | Step of step
  | Step_pop of scope_id * step
  | Directive of directive
type command = { loc : span; command : command_view }
(** [Assume_push] opens a scope before binding its assumption. [Step_pop]
    resolves premises/terms inside that scope, closes it, then binds its result
    in the parent. Declarations/definitions inside a scope also expire on pop.
    Duplicate visible names are refused. Closed sibling scopes may reuse a name
    with a fresh ID (as cvc5 does); active outer names cannot be shadowed. *)
type envelope = Bare | Parenthesized | Unsat_parenthesized
type proof = { envelope : envelope; commands : command list }

type limits = {
  max_bytes : int;
  max_depth : int;
  max_nodes : int;
  max_commands : int;
}
val default_limits : limits
(** Finite resource limits; invalid nonpositive limits produce diagnostics. *)

type directive_check = directive -> (unit, string) result
(** Explicit caller policy for an already pinned signature or checked input
    reference. Default: reject all directives. A successful callback only
    authorizes retaining the directive; it does not validate roots, load a file,
    or change the parser environment. Exceptions from callbacks propagate. *)

val parse_string :
  ?source:string -> ?limits:limits -> ?check_directive:directive_check ->
  string -> (proof, diagnostic) result
val parse_channel :
  ?source:string -> ?limits:limits -> ?check_directive:directive_check ->
  in_channel -> (proof, diagnostic) result
(** Reads to EOF without closing the channel; enforces [max_bytes] while reading. *)
val parse_file :
  ?limits:limits -> ?check_directive:directive_check ->
  string -> (proof, diagnostic) result
(** Opens only the explicitly supplied input path and closes it on return. *)
