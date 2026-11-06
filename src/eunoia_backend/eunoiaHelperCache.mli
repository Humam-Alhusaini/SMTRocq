(** Untrusted, bounded source-helper hints; acceptance remains in Rocq. *)
val api : string -> string
val create : Environ.env -> Common.RocqInterface.constr -> Common.RocqInterface.constr ->
  (string -> EunoiaElaborate.term list -> EunoiaElaborate.term list ->
   (unit -> EunoiaElaborate.term option) -> EunoiaElaborate.term option) *
  ((EunoiaElaborate.term -> Common.RocqInterface.constr) -> Common.RocqInterface.constr list)
