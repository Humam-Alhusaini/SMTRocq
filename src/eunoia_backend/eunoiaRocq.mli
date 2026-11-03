(** Rocq syntax marshaling. Computed syntax is untrusted candidate data. *)
open Common
val global : string -> RocqInterface.constr
val call : string -> RocqInterface.constr list -> RocqInterface.constr
val list : RocqInterface.constr -> RocqInterface.constr list -> RocqInterface.constr
val string : string -> RocqInterface.constr
val term_type : unit -> RocqInterface.constr
val term : EunoiaElaborate.term -> RocqInterface.constr
val term_list : EunoiaElaborate.term list -> RocqInterface.constr
val decode_term : RocqInterface.constr -> EunoiaElaborate.term
val compute_term_option :
  Environ.env -> RocqInterface.constr -> EunoiaElaborate.term option
val checked_true : Environ.env -> RocqInterface.constr -> RocqInterface.constr
(** Checks VM convertibility to true before constructing an equality proof.
    The final tactic uses [Tactics.exact_check], so kernel checking is retained. *)
