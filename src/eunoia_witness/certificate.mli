(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

(** Untrusted local candidates. Only [EunoiaLocal.gate] can accept one. *)
type literal = int
type clause = literal list
type clause_id = int
type lia_proof =
  Common.RocqInterface.Micromega_plugin_Certificate.Mc.zArithProof list

type action =
  | Res of clause_id * clause_id * clause_id
  | CFalse of clause_id
  | CTrue of clause_id
  | BuildDef of clause_id * literal
  | BuildDef2 of clause_id * literal
  | BuildProj of clause_id * literal * int
  | EqTr of clause_id * literal * literal list
  | EqCgr of clause_id * literal * literal option list
  | EqCgrP of clause_id * literal * literal * literal option list
  | LiaMicromega of clause_id * clause * lia_proof

type command = { action : action; expected : clause }
type witness = {
  capacity : int;
  root_claims : (clause_id * clause) list;
  program : command list;
  conflict : clause_id;
}

val output : action -> clause_id
val reads : action -> clause_id list
val canonical : clause -> clause
(** The exact [C.resolve] algorithm; [Res (dst,a,b)] computes [resolve cb ca]. *)
val resolve : clause -> clause -> clause

(** Constructor lookups relative to [EunoiaLocal] and [Checker_Ext]. They must
    resolve actual Rocq constants, not replacements for their computation.
    The corresponding modules must already be loaded in Rocq. *)
val to_coq :
  local:(string -> Common.RocqInterface.constr) ->
  step:(string -> Common.RocqInterface.constr) ->
  witness -> Common.RocqInterface.constr
