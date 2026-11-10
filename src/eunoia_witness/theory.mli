(* Untrusted candidates for the direct verified SMTCoq theory gate. *)
type t = Truth | Identity | Trans | Congruence of int option list | Linear of Certificate.lia_proof
val select : premises:Common.SmtAtom.Form.t list list ->
  conclusion:Common.SmtAtom.Form.t list -> t option
val from_witness : premises:Certificate.clause list -> conclusion:Certificate.clause ->
  Certificate.witness -> t option
val to_coq : constructor:(string -> Common.RocqInterface.constr) ->
  t -> Common.RocqInterface.constr
