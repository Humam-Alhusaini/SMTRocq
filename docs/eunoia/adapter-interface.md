# CPC surface syntax / SMTCoq table adapter

`theories/checker/eunoia/EunoiaAdapter.v` implements a checked structural
boundary for the current generator and core. It does **not** implement the
proof-file reader, a tactic, or complete QF_UF/QF_LIA coverage.

## Entry points and trust boundary

All adapter functions use the existing, authoritative `t_i`, `t_func`,
`t_atom`, and `t_form` tables. Function types come from
`Atom.v_type (t_func.[i])`; atom types and validation use `Atom.get_type`,
`Atom.check_aux`, `Atom.check_atom`, and `Atom.wt`. Formula traversal uses
`Form.lt_form` and `Form.check_form`. This is syntax serialization and partial
typechecking, not another SMT-LIB interpretation.

`EunoiaAdapter.checked_checker` is the concrete entry point. Its arguments are
the four tables, a shared `naming`, fuel, State capacity, authoritative root
clauses, CPC root terms, root slot/clauses claims, a trace, and a conflict slot.
Its trace uses `rule_payload` and `EunoiaBridge.witness`. It supplies **the same
four tables** to the adapter and `EunoiaBridge.gate`, which runs the existing
SMTCoq small checker. Acceptance proves that the authoritative root clauses
cannot all hold under `EunoiaBridge.valuation` of those tables
(`checked_checker_correct`). No generator correctness or type-oracle theorem
is assumed by that result.

The tactic must obtain the authoritative roots from the negated user goal,
using SMTCoq's existing reification/correctness infrastructure. Reading the
solver's `assume` commands as authoritative roots would establish a different
statement and is not an integration of this theorem with the user goal.

`eval : rule_payload -> list C.t -> option C.t` is the core's evaluator after
fixing tables, names, and fuel. A payload contains:

* `rule_name` and explicit `arguments` for `CpcGenerated.derive`;
* exact ordered `premise_terms` from the CPC reader;
* `result_term`, including when a proof step omits its printed conclusion;
* `result_clause`, the precise existing literal sequence claimed for that term.

`eval` checks table validity, binds every supplied premise clause to its CPC
term in order, calls `CpcGenerated.derive fuel (typeof fuel)`, checks the exact
generated result term, and binds the exact result clause to that result.
There is no fallback evaluator, rule-name switch, solver invocation, or
syntax-to-index decoder. Unsupported rules remain generator failures.

The core compares the returned clause with its declared conclusion, then runs
the semantic gate on exactly those premises and conclusion. `check_step_binding`
connects this core acceptance to the adapter's premise and result bindings.
The more general `eval_with_binding` is independent of the candidate-producing
function: even an incorrect candidate producer cannot evade structural binding.
The public `eval` always instantiates it with `CpcGenerated.derive`.

The generic `checker` additionally requires a proved `gate_sound` argument in
its correctness theorem. Integrations should use `checked_checker`, whose
concrete gate is fixed and whose table preconditions are checked executably.
Calling `eval` alone never authorizes insertion into State.

## Shared naming and type query

`naming` has lists of `(Uint63.int * string)` for sort and function names.
These identify existing table entries, including nullary function constants.
`names_wf` rejects out-of-bounds indices, duplicate indices within either map,
duplicate names across both maps, empty names, supported primitive names, and
integer, rational, or decimal literals used as names. Every visited uninterpreted sort or
function needs a map entry. Sort indices are compared in `Z` before conversion
to `Uint63`, preventing wraparound from producing a valid table index.

The reader/reifier must share this map for declarations, aliases, explicit
arguments, roots, premises, and conclusions; it must resolve CPC `define`
aliases to their exact trees. Map entries refer to uninterpreted declarations
from that reification, not to replacement interpretations of CPC built-ins.
The adapter treats strings as already resolved identifiers, not a lexer for
quoted names. It checks consistency and supported primitive collisions; it
does not independently parse the full CPC declaration environment. The reader
must reject redeclarations of signature symbols, including signature symbols
outside this supported fragment. No caller-supplied term-to-literal map is
used as evidence of a binding.

`typeof` is a fuel-bounded structural query using these function signatures.
It checks supported Boolean and integer operators, equal operand types for
equality, branch types for `ite`, UF argument types/arity, supported sorts,
and first-order function type syntax. It returns `None` for unknown syntax,
unknown names, unsupported sorts, or malformed applications. Its result is
executable input to the generated evaluator, never semantic evidence.

The query also recognizes CPC's `@List`/`@list.nil`/`@list` aliases from
`programs/Utils.eo`, and `Real` literal categories declared in
`theories/Arith.eo`. List elements must each have a known syntax type, though
those types may differ. Nested lists are allowed; unknown elements and malformed
numeric literals reject. Rational and decimal literal spellings retain the
`Real` category even when their value is integral. This extends only the
signature argument query: it adds no `Typ.type` constructor, Atom/Form encoding,
or interpretation for object-level real arithmetic. Such unsupported object
expressions still reject. The new metadata names are reserved against naming
collisions. The original Boolean/integer/UF query supplies all object types.

## Exact surface encodings

`app s [a; b; ...]` is a left-curried `Apply` tree rooted at `Symbol s`.
It preserves operand order, nesting, and literal polarity. It does not perform
commutativity, associative flattening, nil insertion, constant evaluation,
De Morgan rewriting, implication expansion, or double-negation elimination.

Supported serialization includes:

* UF constants/applications, equality over supported sorts, `Bool`, `Int`,
  and named uninterpreted sorts;
* integer zero and the existing internal positive numeral DAG; `UO_Zpos` and
  `UO_Zneg` become canonical signed decimal symbols, while `UO_Zopp` remains an
  explicit unary `-` application;
* binary integer `+`, `-`, `*`, `<`, `<=`, `>`, `>=` (syntax only; nonlinear
  multiplication is not claimed as checked LIA coverage);
* formula `true`, `false`, negated literals, `Fnot2` as the specified number of
  explicit double negations, `and`, `or`, `=>`, `xor`, Boolean equality, and
  Boolean `ite`.

All recursive table reads are bounded and obey the existing strict dependency
order. Non-Boolean `Fatom`, ill-typed atoms, invalid UF arity, missing names,
cycles, unsupported array/BV/bit-blasting constructors, and exhausted fuel
reject. N-ary formula nodes with fewer than two arguments reject instead of
guessing a surface identity or removing a node. Internal positive numeral
nodes have no independently exposed CPC sort.

Clause encoding is explicit:

| Precise `C.t` | Surface term |
| --- | --- |
| `[]` | `Symbol "false"` |
| `[l]` | exact encoding of literal `l` |
| `[l1; l2; ...]` | flat curried `or` applied to those literal encodings |

`binds` also requires the clause to already equal `S.sort c` and every literal
index to be in bounds. It never sorts a CPC operand list to obtain a match.
For a disjunction with a different operand order, the reader can claim a
singleton literal for the corresponding `Form.For` node if one exists;
otherwise the step rejects.

Consequently both a singleton literal for `Form.For [p; q]` and the clause
`[p; q]` can serialize to `(or p q)`. Similarly, both `[]` and a singleton
literal for `Form.Ffalse` serialize to `false`. **Encoding is not injective.**
The explicit result clause, literal-for-literal core comparison, and semantic
gate keep those representations distinct. In particular `[false_literal]`
does not satisfy the core's empty-clause conflict test. Neither `(not true)`
nor a normalized nil-terminated `or` is accepted as an alternative spelling.
`binds_spec` and `bind_terms_spec` prove exact checked-encoding relationships,
including list lengths and order; they do not assert injectivity.

## Remaining interfaces and integration work

1. The current generator fragment deliberately rejects associative-nil
   declarations. A flat `(or p q)` differs from `(or p (or q false))`, as does
   `(+ n 1)` from its CPC associative-nil expansion. The adapter does not repair
   this by changing signature syntax. Broader generated support needs an
   explicitly agreed reader/signature representation, with checked bindings
   for every permitted representation. Existing signed numeral `-2` also
   differs from explicit `(- 2)`; tables must preserve that distinction.
2. Every result must already have its atoms/forms in the common tables. The
   reader must expand aliases, obtain omitted generated conclusions, and
   reify all needed terms without allowing a supplied mapping to replace the
   checked serialization. There is no lazy table mutation inside `eval`.
3. A single old checker step often does not produce a CPC formula's singleton
   clause. For example, an EUF congruence checker generally emits an implication
   clause without reading State premises, whereas CPC `cong` concludes an
   equality using earlier equality proofs. A local multistep semantic witness
   may need to create the EUF lemma and resolve it against exactly the listed
   premises. Such an extension must prove the exact read footprint, initialization,
   intermediate validity, and exact final result. Extra roots or an independent
   solver refutation are not substitutes. That extension is not implemented here.
4. The coordinator must integrate reader/tactic wiring and the theory stanza.
   The existing core-owned `SMTCoq.checker.eunoia` stanza, with `Stdlib`,
   `SMTCoq.utils`, `SMTCoq.structures`, `SMTCoq.checker.fol`, and `SMTCoq.checker`,
   already lists the needed dependencies once all source modules are integrated.
   This child changes no dune, generator, core, bridge, or tactic files.
5. No actual `uf4` CPC trace, full LIA trace, tactic invocation, benchmark, or
   full backend completion is claimed by the examples below.

## Validation and dependency versions

Tested with private `/home/charles/code/friends/.toolchains/smtrocq-env`:
Rocq 9.3.0, OCaml 4.14.2. The base checkout is `cfd4e07`.

Read-only dependency versions, copied only to `/tmp/smtrocq-adapter-check`:

* Generator: `a83ec1e55f4888de2568a8ad7c088d9dd415e496`, worktree
  `/home/charles/.t3/worktrees/SMTRocq/t3-08d3adb3`.
* Core/bridge: `4306d4d4b5e5402a3b02bda66133880d5d78b19e`, worktree
  `/home/charles/.t3/worktrees/SMTRocq/t3-79625ab5`.
* Existing SMTCoq compiled dependencies: that core worktree's
  `_build/default/theories`; no snapshots are committed with this adapter.

Snapshot SHA256 values (also matched the owners' committed files):

```text
ba5c2efebffbe50b7f0b361cd070bf341c877f30bca58b352f0b3087a0d91e99 EoSyntax.v
5f42354fa23cef8133481f2d0d5ad702f1b69537139f027f51d385cc4455dfae EoRuntime.v
ea2be8c3b1a5bdff01820456c598e6b7be17adddb538d5612c63cee65e02468e CpcGenerated.v
0c74f7e18383c14cbaec3cdc3e6d312fa4d877de679a5a2b9e3fdbfcea2f28d2 EunoiaChecker.v
69ee2b36b2e9927336573e2bd46863f167cd97386396b347d43baa720aec532c EunoiaBridge.v
```

The reproduction driver is `/tmp/smtrocq-adapter-check/check.py`; it runs
`smtrocq-env rocq c` sequentially on `EoSyntax.v`, `EoRuntime.v`,
`CpcGenerated.v`, `EunoiaChecker.v`, `EunoiaBridge.v`, and `EunoiaAdapter.v`.
Each exact invocation and exit code is in
`/tmp/smtrocq-adapter-check/compile.log`. Existing top-level checker `.vo` files
are copied to `/tmp/smtrocq-adapter-baseline-checker` to avoid a recursive
`-Q` mapping importing two copies of `EunoiaChecker`.

The complete setup and compiler commands are:

```sh
mkdir -p /tmp/smtrocq-adapter-check /tmp/smtrocq-adapter-baseline-checker
cp /home/charles/.t3/worktrees/SMTRocq/t3-08d3adb3/theories/checker/eunoia/{EoSyntax,EoRuntime,CpcGenerated}.v /tmp/smtrocq-adapter-check/
cp /home/charles/.t3/worktrees/SMTRocq/t3-79625ab5/theories/checker/eunoia/{EunoiaChecker,EunoiaBridge}.v /tmp/smtrocq-adapter-check/
cp theories/checker/eunoia/EunoiaAdapter.v /tmp/smtrocq-adapter-check/
cp /home/charles/.t3/worktrees/SMTRocq/t3-79625ab5/_build/default/theories/checker/*.vo /tmp/smtrocq-adapter-baseline-checker/
python3 /tmp/smtrocq-adapter-check/check.py > /tmp/smtrocq-adapter-check/compile.log 2>&1
```

Driver contents, using only private compiler/dependency paths:

```python
from pathlib import Path
import subprocess
base = Path('/home/charles/.t3/worktrees/SMTRocq/t3-79625ab5/_build/default/theories')
tmp = Path('/tmp/smtrocq-adapter-check')
flags = []
for path, logical in [('utils', 'SMTCoq.utils'), ('structures', 'SMTCoq.structures'),
                      ('checker/fol', 'SMTCoq.checker.fol')]:
    flags += ['-Q', str(base / path), logical]
for name in ['array', 'bva', 'cnf', 'euf', 'lia', 'spl']:
    flags += ['-Q', str(base / 'checker' / 'small-checkers' / name),
              'SMTCoq.checker.small_checker.' + name]
flags += ['-Q', '/tmp/smtrocq-adapter-baseline-checker', 'SMTCoq.checker']
flags += ['-Q', str(tmp), 'SMTCoq.checker.eunoia']
for name in ['EoSyntax', 'EoRuntime', 'CpcGenerated', 'EunoiaChecker',
             'EunoiaBridge', 'EunoiaAdapter']:
    cmd = ['/home/charles/code/friends/.toolchains/smtrocq-env', 'rocq', 'c']
    cmd += flags + [str(tmp / (name + '.v'))]
    print('COMMAND:', ' '.join(cmd), flush=True)
    result = subprocess.run(cmd, cwd=tmp)
    print('EXIT:', result.returncode, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
```

Final compiler run: exit **0**; each of the six individual module invocations
also exited **0**. All **49** examples in `EunoiaAdapter.Examples` use
`vm_compute; reflexivity` (with a conjunction split where needed), checked by
the kernel. They cover positive UF, integer, and Boolean bindings; negative
bounds/type/arity/cycle/name/order/polarity/syntax/fuel cases; actual generated
`refl` and `contra`; and a `contra` trace accepted through the concrete existing
resolution gate. Altering its CPC root term rejects.

Independent recursive kernel rechecking also exited **0**, using the same load
paths and no dependency-admission flags. Exact command/output:
`/tmp/smtrocq-adapter-check/kernel.log`. The invocation was:

```sh
python3 - <<'PY' > /tmp/smtrocq-adapter-check/kernel.log 2>&1
from pathlib import Path
import subprocess
source = Path('/tmp/smtrocq-adapter-check/check.py').read_text()
exec(source.split("for name in ['EoSyntax'")[0])
cmd = ['/home/charles/code/friends/.toolchains/smtrocq-env', 'rocq', 'check', '-silent'] + flags + ['SMTCoq.checker.eunoia.EunoiaAdapter']
print('COMMAND:', ' '.join(cmd), flush=True)
result = subprocess.run(cmd, cwd=tmp)
print('EXIT:', result.returncode, flush=True)
raise SystemExit(result.returncode)
PY
```

The source runs `Print Assumptions` for all eight new lemmas/theorems:
`term_eqb_spec`, `binds_spec`, `bind_terms_spec`, `eval_with_binding`,
`check_step_binding`, `checker_correct`, `checker_root_binding`, and
`checked_checker_correct`. Their exact outputs are in `compile.log` and the
labelled `/tmp/smtrocq-adapter-check/assumptions.txt`.

`term_eqb_spec` is closed under the global context. The others retain existing
Uint63 primitives/specifications and `ProofIrrelevance.proof_irrelevance`
through SMTCoq's existing dependent type interpretation. The concrete
`checked_checker_correct` additionally inherits the existing arithmetic and
bitwise primitive specifications used by `MainChecker` (including division,
carry operations, shifts, and leading/trailing zero counts). No new axiom,
parameter, solver assumption, or proof hole is introduced. These theorems are
not advertised as axiom-free; `BEST_PRACTICE.md` permits the inherited Int63
and carefully used existing proof irrelevance infrastructure.

`rg -n '\b(Admitted|admit|Axiom|Parameter|Abort)\b' theories/checker/eunoia/EunoiaAdapter.v`
returned **1** with no matches. Whitespace checks returned **0** with no
diagnostics. No dune or repository-wide regression build was run in this
child: compilation and independent kernel checking use isolated dependency
copies, leaving shared build ownership with the coordinator.

For syntax reconnaissance only, cvc5 1.4.2 (`282d5e0`) was invoked as follows;
it exited **0**, printed `unsat` and a CPC trace containing both `(- 2)` and
the evaluated literal `-2`. This solver output is not accepted by the adapter
as a proof and supplies no soundness assumption:

```sh
/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5 --lang=smt2 --dump-proofs --proof-format=cpc <<'EOF'
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- 2)))
(assert (> x 0))
(check-sat)
EOF
```

The matching signature was read from
`/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/`;
neither Ethos nor Logos was used for this adapter implementation.
