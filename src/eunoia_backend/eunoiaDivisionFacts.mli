(** Proved Boolean facts about actual Rocq division/modulo, abs, min, max and sign. Symbolic divisors use
    conditional bounds or a supplied, proved equality to a ground divisor. Returns proof terms, never assumptions or checker successes.
    Instances are deduplicated and bounded; binders/branches are not traversed. *)
val collect : Environ.env ->
  equalities:(Common.RocqInterface.constr * Common.RocqInterface.constr) list ->
  Common.RocqInterface.constr list -> Common.RocqInterface.constr list
