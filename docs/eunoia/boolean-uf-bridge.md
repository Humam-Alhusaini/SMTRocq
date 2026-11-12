# Typed Boolean arguments in UF congruence

This is the checker-side handoff for the Boolean-argument gap at base
`8a739b7`. It adds only `EunoiaBool.v`, `EunoiaBoolTests.v`, and this document.
The public tactic, producer, compiler, and local witness gate are unchanged.
Public `cvc5_eunoia` acceptance of the original goal still requires integration.

## Existing verified operations inspected

`EUF.get_eq` recognizes only `Fatom (Abop (BO_eq _) a b)`.
`EUF.build_congr_correct` propagates equality of interpreted atom values;
`valid_check_congr` and `valid_check_congr_pred` establish its congruence
clauses. Their syntax does not accept the `Fiff` used for Boolean equality.
CNF's `Fiff` definition/projection clauses relate formula truth values, not
the typed atom values needed as function arguments. They cannot supply the
missing link on their own.

`Atom.interp_bool` projects a Boolean value, but returns `true` on values of
other types. Thus `Fiff (Fatom x) (Fatom y)` can be true for unequal integer
atoms. The tests demonstrate this with integer values zero and one. Treating
arbitrary such forms as atom equality would be unsound.

The bridge uses `Atom.check_aux_interp_hatom`, `Atom.t_interp_wf`,
`Form.check_form_correct`, `Form.wf_interp_form`, `Typ.cast_refl`,
`Typ.i_eqb_spec`, and `Atom.Bval_inj2`. It defines no SMT-LIB interpretation.
It leaves the existing EUF/CNF code unchanged and uses their Atom/Form/Typ
semantics directly.

## Proven API

All functions below take the existing tables in this order:
`t_i`, `t_func`, `t_atom`, `t_form` (except helpers whose unused arguments
Rocq omits). Names are exported in module `EunoiaBool`.

```coq
equality_view : _lit -> option (Atom.hatom * Atom.hatom)
argument_clause : list (option _lit) -> list Atom.hatom ->
                  list Atom.hatom -> option C.t
congr_clause : _lit -> list (option _lit) -> option C.t
check_congr : _lit -> list (option _lit) -> C.t -> bool
```

With `h := Atom.interp_hatom t_i t_func t_atom` and
`rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
(Atom.interp_form_hatom_bv t_i t_func t_atom) t_form`, the principal contracts
are:

```coq
equality_view_sound :
  Atom.check_atom t_atom -> Form.check_form t_form ->
  equality_view l = Some (a,b) ->
  (Lit.interp rho l = true <-> h a = h b)

argument_clause_sound :
  Atom.check_atom t_atom -> Form.check_form t_form ->
  argument_clause eqs xs ys = Some c ->
  C.interp rho c = false -> map h xs = map h ys

congr_clause_sound :
  Atom.check_atom t_atom -> Form.check_form t_form ->
  congr_clause res eqs = Some c -> C.valid rho c

check_congr_sound :
  Atom.check_atom t_atom -> Form.check_form t_form ->
  check_congr res eqs expected = true -> C.valid rho expected
```

These are schematic displays of explicit theorem arguments, not additional
assumptions or declarations. Each endpoint type is checked using the existing
`Atom.get_type`; no caller-provided type annotation is trusted. Accordingly,
these local lemmas do not require global `Atom.wt`. The enclosing production
checker must retain its existing `Atom.wt` obligation and authoritative
reification checks.

`equality_view` accepts either:

* A positive `Fatom` containing `BO_eq t`, with both atom endpoints in bounds
  and of actual interpreted type `t`.
* A positive `Fiff p q`, where both operands are positive, bounded `Fatom`
  literals whose atom indices are bounded and whose actual types are Boolean.

Negative equality literals, negative `Fiff` operands (including two negative
operands), constants as operands, compound-form operands, and malformed bounds
return `None`. No polarity is erased. Both false Boolean endpoints count as
equal. A false equality premise remains a conditional hypothesis: its negation
appears in the clause, and its endpoints need not be equal unconditionally.

`congr_clause` requires two `Aapp` endpoints with the same bounded function
index. It accepts arbitrary result sorts, arbitrary arity, and mixed argument
sorts. Each argument has exactly one optional equality witness. `None` requires
identical bounded atom indices; `Some l` requires a checked equality with the
same endpoints in either orientation. Missing, extra, disconnected, or
out-of-bounds evidence fails. The output is the **raw ordered clause**
`res :: map Lit.neg used_equalities`, in argument order, omitting `None`.
`check_congr` compares this raw clause exactly, including order and signs.
Failures are explicit `None`/`false`, with no `C._true` fallback.

For the actual Boolean encoding, let formulas 2 and 3 be `Fatom a`, `Fatom b`;
formula 4 be `Fiff 4 6`; formulas 5 and 6 be `Fatom (f a)`, `Fatom (f b)`;
and formula 7 be `Fiff 10 12`. Then:

```coq
congr_clause 14 [Some 8] = Some [14;9]
```

The exported `boolean_uf_semantic_clause` proves exactly this clause using
the checker theorem, over symbolic values/functions, checked formula/atom
tables, and an independently computed `Atom.wt` test. `boolean_uf_target`
derives `a = b -> f a = f b` from that semantic clause.

## Integration patch proposal and ownership handoff

A new semantic operation is needed: existing `Checker_Ext.step` commands
cannot express this certificate. Keep it local to Eunoia rather than changing
the general MainChecker witness language. The gate owner should add a command
alternative, schematically:

```coq
CoreCommand : existing_command -> local_command
BoolCongrCommand : clause_id -> _lit -> list (option _lit) -> C.t -> local_command
```

Adapt `witness.program`, serialization, and the execution proof to that local
sum. Preserve the old branch unchanged. For the new branch:

1. Require a fresh bounded output slot and all explicit formula references
   bounded, as for existing commands. Run this check on every command,
   including unused commands and commands after conflict.
2. Recompute `EunoiaBool.congr_clause t_i t_func t_atom t_form res eqs`.
   Reject `None`. Obtain `C.valid rho raw` from `congr_clause_sound` using the
   gate's existing table checks.
3. Store `raw` with existing `S.set_clause`; use its existing validity theorem.
   This canonicalizes through `S.sort`, just as the old semantic operations do.
   Check the stored result against the command's canonical `expected`, require
   `clause_wf`, and retain the existing rejection of `C._true` results.
   Do **not** feed canonical `expected` directly to `check_congr`, which checks
   raw order. No new semantic theorem for clause sorting is necessary.
4. Mark the slot live only after success. Preserve exact local roots, ordered
   premise binding, fresh outputs, recursive execution, and final empty-clause
   checks. This operation reads no clause slots: its equalities are conditional
   clause literals, discharged by subsequent ordinary local resolutions.

For the example, add the congruence clause `[14;9]` to local roots `[8]` and
`[15]`, resolve against `[8]` to obtain `[14]`, then against `[15]` to obtain
`[]`. The producer should discover typed `Fiff` equality edges and emit the
new command when legacy `EqCgr` cannot represent them. It must retain the
exact result orientation and every used premise. Search remains untrusted;
the new checker, existing resolutions, and the generated CPC step binding
must all accept. No synthetic Boolean `BO_eq` atoms or table extensions are
needed.

Requested ownership handoff: `EunoiaLocal.v` and its tests to the gate owner;
the witness search, witness serialization/compiler, and corresponding native
tests to the producer/compiler owners. Register `EunoiaBoolTests.vo` in the
shared `theories/checker/eunoia/dune` runtest alias. The existing theory stanza
already discovers and installs both new modules. Add live public-tactic
tests for Boolean inputs/outputs, Boolean inputs/integer outputs, mixed
arguments, and false-valued inputs, then rerun the parent's UF22/LIA15 suites.
No shared file is edited by this handoff.

## Validation and remaining scope

There are 44 executable examples and two exported semantic lemmas. Tests include
typed tables, the previously rejected legacy EUF operation, generic UF
congruence, real false-valued inputs, false premises, non-Boolean projection
counterexamples, polarity, bounds, malformed evidence, and exact clause
mutations. Every new checker lemma and both exported semantic test lemmas
have `Print Assumptions` commands, as do the three concrete interpretation
examples for false endpoints, non-Boolean projection, and false premises.

Final verification uses only
`/home/charles/code/friends/.toolchains/smtrocq-env` (Rocq 9.3.0, OCaml 4.14.2).
All paths below are local to the prepared worktree or `/tmp`. Commands run
from the repository root:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EunoiaBool.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EunoiaBoolTests.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
```

Each final command exited 0. Logs, respectively:
`/tmp/eunoia-bool-build.log`, `/tmp/eunoia-bool-tests-final.log`,
`/tmp/eunoia-bool-install-final.log`. The first two contain the explicit
assumption-print output. Earlier development compiles failed on proof-script
and test-proof errors, subsequently corrected; an initial install build
exited 1 while those files were changing. Two redundant pending target builds
were interrupted (exit 130); the final single target/install builds above
supersede them. No development failure was accepted as a positive test.

The exact checker audit command (exit 0) is:

```sh
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaBool \
  --theorem EunoiaBool.form_unfold \
  --theorem EunoiaBool.atom_unfold \
  --theorem EunoiaBool.typed_pair_types \
  --theorem EunoiaBool.atom_view_sound \
  --theorem EunoiaBool.boolean_values \
  --theorem EunoiaBool.atomic_equality \
  --theorem EunoiaBool.equality_view_sound \
  --theorem EunoiaBool.endpoints_sound \
  --theorem EunoiaBool.argument_clause_sound \
  --theorem EunoiaBool.congr_clause_sound \
  --theorem EunoiaBool.check_congr_sound \
  --output-dir /tmp/eunoia-bool-assumptions
```

Its log is `/tmp/eunoia-bool-audit.log`; `summary.json`, the compiler command,
compiler log, and eleven individual qualified-assumption reports are in
`/tmp/eunoia-bool-assumptions/`. All eleven pass with zero additions to the
52-entry baseline (their union is exactly that baseline).

The semantic-test audit command is:

```sh
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaBoolTests \
  --theorem EunoiaBoolTests.boolean_uf_semantic_clause \
  --theorem EunoiaBoolTests.boolean_uf_target \
  --theorem EunoiaBoolTests.false_false_equality_accepted \
  --theorem EunoiaBoolTests.nonboolean_projection_is_really_true \
  --theorem EunoiaBoolTests.false_premise_is_conditional \
  --output-dir /tmp/eunoia-bool-test-assumptions
```

Log: `/tmp/eunoia-bool-test-audit.log`; full reports and `summary.json`:
`/tmp/eunoia-bool-test-assumptions/`.

The independent **recursive** kernel check uses neither `-admit` nor `-norec`:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  SMTCoq.checker.eunoia.EunoiaBool SMTCoq.checker.eunoia.EunoiaBoolTests
```

Log: `/tmp/eunoia-bool-tests-recursive-check.log`. A separate recursive check
of `EunoiaBool` alone already exited 0; its log is
`/tmp/eunoia-bool-recursive-check.log`. `git diff --check` also exited 0.
Static inspection found no forbidden declarations/proof holes or use of
`array_ext` in either new theory. After adding the three concrete-example
assumption prints, the final combined build command was:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  theories/checker/eunoia/EunoiaBoolTests.vo @install
```

Log: `/tmp/eunoia-bool-final-build.log`.

The final combined build exited 0. The expanded semantic-test audit exited 0
(`compiler_exit_code: 0`, `passed: true`, five reports, zero new assumptions).
The combined recursive check also exited 0 with an empty diagnostic log.

The certificate currently covers `Aapp` congruence, not interpreted operator
congruence, transitivity search, signed formula operands, formula constants
as atom arguments, arbitrary compound Boolean terms without a reified atom,
or a public tactic integration. Those are explicit remaining limits. Type
checks evaluate the existing interpreted atom table; no performance claim
is made. There are no new assumptions, proof holes, trusted hooks, array
extensionality dependencies, solver installs, backend changes, pushes, or PRs.
