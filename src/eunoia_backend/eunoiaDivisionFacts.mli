(** Proved Boolean facts about actual Rocq division/modulo by ground integer
    divisors. Returns proof terms, never assumptions or checker successes.
    Instances are deduplicated and bounded; binders/branches are not traversed. *)
val collect : Environ.env -> Common.RocqInterface.constr list -> Common.RocqInterface.constr list
