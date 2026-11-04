(** Untrusted CPC production. No shell, PATH lookup, or solver-result acceptance. *)
type limits = {
  wall_seconds : float;
  solver_milliseconds : int;
  resources : int;
  max_bytes : int;
}
val default_limits : limits
val toolchain_root : unit -> string
val binary : unit -> string
val signature : unit -> string
exception Error of string
val run : ?limits:limits -> string -> Eunoia_frontend.EunoiaProof.proof
(** Input must come from the table-based exporter. Requests CPC with trust
    disabled. Requires exit 0 and the unsat CPC envelope, parses to EOF, and
    cleans and reaps the private process even on exceptions. Still UNCHECKED. *)
