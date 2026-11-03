open Common

type tables = {
  sorts : SmtBtype.reify_tbl;
  functions : SmtAtom.Op.reify_tbl;
  atoms : SmtAtom.Atom.reify_tbl;
  forms : SmtAtom.Form.reify;
}

type witness_producer =
  atoms:SmtAtom.Atom.reify_tbl -> forms:SmtAtom.Form.reify ->
  premises:SmtAtom.Form.t list list -> conclusion:SmtAtom.Form.t list ->
  (RocqInterface.constr, string) result
(** Candidate constructor for [EunoiaLocal.witness]. Called for EVERY CPC step,
    including unused ones. Final checking reruns the generated evaluator, exact
    adapter bindings, and [EunoiaLocal.gate] for the whole trace. *)

val create_tables : unit -> tables
val export : tables -> SmtAtom.Form.t list -> string
(** Existing SMTCoq type/formula printers; no solver declarations are imported. *)

val build_refutation :
  ?limits:EunoiaSolver.limits -> ?fuel:int -> witness:witness_producer ->
  Environ.env -> tables -> SmtAtom.Form.t list -> RocqInterface.constr
(** Returns a checked proof of [~ Forall (C.valid valuation) (map singleton roots)].
    Calls the private solver and elaborates every command. Requires loaded
    EunoiaTactic, EunoiaAdapter, EunoiaLocal, and generated syntax/evaluator modules.
    This uses EunoiaTactic.checker with its fixed proved multi-operation gate. *)

val build_refutation_from_cpc :
  ?fuel:int -> witness:witness_producer -> Environ.env -> tables ->
  SmtAtom.Form.t list -> Eunoia_frontend.EunoiaProof.proof -> RocqInterface.constr
(** Offline replay through exactly the same generated checker and gates. *)

val tactic :
  ?limits:EunoiaSolver.limits -> ?fuel:int ->
  ?preprocess:RocqInterface.tactic -> witness:witness_producer ->
  ?lemmas:RocqInterface.constr list -> unit -> RocqInterface.tactic
(** Checked Boolean equality/is_true tactic, after optional existing
    preprocessing. Reuses existing reification and supplied lemma proofs;
    rejects missing CompDec cuts and quantified lemmas. Uses the concrete
    EunoiaTactic.checker_b/checker_eq correctness targets and [exact_check].
    There is no no-check variant or legacy trace fallback. *)

val tactic_from_cpc :
  Eunoia_frontend.EunoiaProof.proof -> ?fuel:int ->
  ?preprocess:RocqInterface.tactic -> witness:witness_producer ->
  ?lemmas:RocqInterface.constr list -> unit -> RocqInterface.tactic
(** Checked replay tactic; useful for reproducible solver-independent tests.
    Roots still come from the current goal and supplied lemma proofs. *)
