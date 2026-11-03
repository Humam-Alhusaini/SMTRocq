# Untrusted CPC proof text frontend

`src/eunoia/eunoiaProof.ml` and its documented `.mli` provide a standalone OCaml
reader for a strict, signature-independent subset of CPC proof text. The library
is `rocq-smtcoq.eunoia_frontend`, with module
`Eunoia_frontend.EunoiaProof`. It has no Rocq, solver, generated-signature, or
third-party OCaml dependencies. Its isolated `src/eunoia/dune` stanza does not
change the shared plugin/tactic stanzas.

**Parsing is not proof validation.** An `Ok` result only means that the text,
command structure, scopes, and named premise references were read successfully.
An empty command stream, a step claiming `true`, an unknown rule, or a `trust`
step can parse. No command or step is filtered out, no inference is performed,
and no solver result is used as evidence. This frontend adds no soundness lemma
or Rocq assumption; `Print Assumptions` therefore has no new target here.

## API and integration contract

The entry points are `parse_string`, `parse_channel`, and `parse_file`, each
returning `(proof, diagnostic) result`. Channel input is read to EOF without
closing the supplied channel. File input opens only the explicitly supplied
path and closes it even if a policy callback raises. Diagnostics carry a source
name and start/end byte positions with one-based lines and columns (LF lines).
Use `pp_diagnostic` to print `source:line:column: message`.

The returned proof records its input envelope and every command in source order:

* `Declare`: `declare-sort`, `declare-const`, or `declare-fun`, with raw sort
  syntax, a unique binding ID, and its current scope.
* `Define`: `define` with typed parameters and a syntax body. Both nullary
  shared terms and parameterized macros are retained, without expansion.
* `Assume`: a global root assumption and formula.
* `Assume_push`: a scope ID and local assumption.
* `Step`: unique proof ID, rule symbol, ordered arguments and premises, and an
  optional claimed conclusion.
* `Step_pop`: the closed scope ID and a step bound in its parent scope.
* `Directive`: an explicitly policy-approved include/reference, retained rather
  than discarded.

Terms distinguish symbols (including their quoting), exact literal spellings,
applications, and parallel `let` bindings. `Name (_, Some id)` resolves to a
preceding visible declaration/definition or lexical binder. `Name (_, None)`
is unresolved signature syntax: the elaborator must consult only its pinned
signature, never retrospectively bind it to a later proof-file declaration.
This also prevents definitions from acquiring later bindings at use sites.
Definition parameters and `let` binders have unique binding IDs. Macro bodies
capture the environment at their declaration and are not expanded by the reader.
Parameter sorts are read sequentially, with preceding parameters visible.

Premises carry both their original symbol/location and a resolved `proof_id`.
IDs are fresh reader identities, not the integer suffix of `@p47`, a checker
state index, or a stack offset. Premise order and multiplicity are preserved.
Future, dangling, expired, self, and term-as-proof premise references fail.

The coordinator must supply the remaining adapter in shared dune/tactic files:

1. Add `eunoia_frontend` to the consuming library's dependencies and use
   `Eunoia_frontend.EunoiaProof`. No changes to shared `src/dune` or
   `g_smtcoq.mlg` have been made here.
2. Elaborate every term, declaration, definition, rule, argument list, and side
   condition against the generated syntax of the pinned actual CPC signature.
   Reject unknown symbols/rules and unsupported terms; there is no manual CPC
   rule switch in this reader. Map reader IDs to the core's IDs explicitly.
3. Bind **every** global assumption to the actual reflected input. The reader
   does not decide whether two formulas are equivalent or whether a root belongs
   to the query. Do not turn an unmatched root into an extra assumption.
4. Preserve and check every step, including scope operations. Check a stated
   conclusion against the computed/checked result whenever present. A missing
   conclusion means the rule must compute it; it never means skip the step.
5. Enforce discharge and visibility of local assumptions/declarations, and the
   semantic conditions for scope export. The reader resolves references but does
   not justify a scope rule or export a local fact semantically.
6. Require a checked refutation using the existing SMTCoq semantics/checkers.
   Neither the `unsat` envelope nor the presence of a literal `false` establishes
   this condition. Unknown and `trust` rules must fail unless the eventual
   generated/checker path supplies a checked justification for that exact step.

## Text and scope policy

The reader accepts a bare command sequence, a single parenthesized sequence,
and the actual cvc5 response `unsat` followed by a parenthesized sequence. It
requires EOF: trailing tokens, unmatched parentheses, multiple responses,
`sat`, `unknown`, and solver error commands fail. Empty streams parse as empty
syntax; the integration must reject them as refutations.

Line comments beginning with `;` are accepted, including comments at EOF. Strings
retain SMT-LIB doubled quotes and backslashes exactly. Unicode string escape
semantics belong to later signature-directed elaboration. Quoted symbols lose
only their `|` delimiters and retain a `quoted` flag; quoted and bare symbols
with the same contents have the same name identity. Backslash escapes and
control bytes in quoted symbols are unsupported and rejected. Strings cannot
be mistaken for identifiers or command fields. Sexplib block/discard comments
are rejected, since silently consuming commands would be unsafe.

Numerals (including cvc5 negative spellings), decimal/fractional rationals,
binary/hex literals, and strings have distinct constructors. A zero rational
denominator and malformed literal tokens fail. Higher-order/indexed/ascribed
application syntax is preserved structurally, without desugaring `_` or `as`.
Only explicit parallel `let` is elaborated into lexical bindings. Binder and
annotated forms `forall`, `exists`, `lambda`, `match`, `par`, and `!` are rejected
in this initial QF subset. Empty applications/terms are rejected.

`assume-push` opens a lexical scope; its assumption and subsequent declarations,
definitions, and proof steps expire when the matching `step-pop` closes it.
Pop premises, arguments, and the claimed conclusion resolve inside the scope;
the new proof ID is bound after restoring the parent environment. All visible
name collisions fail (including term/proof collisions, declaration overloading,
and active outer-name shadowing). Names may be reused after the introducing
scope has closed, with fresh IDs: cvc5 does this in the actual LIA fixture.
`let` and definition parameters allow lexical shadowing but reject duplicate
names in one binder list. Every global `assume` must precede steps/scopes.
Unmatched pops, unclosed scopes, and SMT-LIB `push`/`pop` fail.

Only the documented command forms are accepted. Unknown commands, datatypes,
signature/rule/program declarations, recursive definitions, declaration or
definition attributes (including `:type`, `:global`, and `:local`), malformed
fields, duplicate step fields, and reference normalization routines fail.
Local/global declaration lifetime is represented by scope IDs, without adding
an invented declaration attribute. `:rule`, `:premises`, and `:args` may occur
in any order, at most once each; `:rule` is required.

## Include/reference policy

Default policy rejects both directives. An optional `check_directive` callback
must explicitly authorize each `Include path` or `Reference path`. A caller
should use a read-only exact-match policy only after pinning the loaded signature
or independently checking the referenced input; parser success is not that
check. Callback rejection is a located error and callback exceptions propagate.

Approved directives remain in the AST and do not open files or mutate the
reader's symbol tables. There is no arbitrary filesystem traversal or recursive
include mechanism. Directives must precede all other commands; duplicate
includes and more than one reference fail. Paths must be nonempty, unescaped
strings without control bytes. Reference normalization is unsupported. An
approved reference still obliges the consumer to bind every root to the actual
input; it never authorizes dropping assumptions or skipping that check.

## Resource limits and remaining limitations

Default limits are 64 MiB input, 512 levels of syntax nesting, two million syntax
nodes, and one million commands. Positive custom limits are accepted. String
and channel/file entry points enforce the input size bound; wide syntax and
command maps use tail-recursive traversals on OCaml 4.14. The frontend still
holds the bounded input, syntax tree, and output in memory; it is not a streaming
checker. UTF-8 and theory-specific literal decoding/type checking are left to
elaboration. Symbol overloading, active-name shadowing, full Eunoia signature
syntax, quantifiers, datatypes, and incremental SMT-LIB queries remain unsupported.
There is no tactic integration, generated-term adapter, semantic scope checking,
root validation, or CPC proof validation in this change.

## References and regression fixtures

Local read-only references inspected:

* Logos `/tmp/smtrocq-logos`, commit
  `89df5909b0e9aabb936b68ee95c75a18f609db7a`: `docs/parser.md`,
  `Logos/Parser/Core.lean`, `Logos/Sexp.lean`, `test/CpcParser.lean`, and the
  scope/define/string regression inputs. In particular its documented
  include/reference ignoring policy is **not** copied here.
* Ethos `/tmp/smtrocq-ethos`, commit
  `f97393ea55f03653689e104d0e9c9010ee17780c`: `user_manual.md`,
  `src/cmd_parser.cpp`, and `src/state.cpp`, for scope restoration, optional
  conclusions, definition grammar, and reference-input obligations.
* cvc5 1.4.2 (`--version`: git `282d5e0`); matching signature
  `/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo`.

`src/eunoia/tests/fixtures/` contains exact cvc5 dumps, with source SMT-LIB:
`uf4` from `unit-tests/files/uf4.smt2`, `lia1` from
`unit-tests/files/lia1.smt2`, and a new two-bound `lia-small` example. The latter
contradicts `x >= 3` and `x <= 2`. `lia1` exercises nested scopes, nonmonotonic
numeric proof names, and reuse of names in separate closed scopes. These are
parser fixtures, not certificates accepted by this implementation.

Reproduce each fixture from the repository root (each command must return 0):

```sh
CVC5=/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5
for name in uf4 lia-small lia1; do
  "$CVC5" --dump-proofs --proof-format=cpc "src/eunoia/tests/fixtures/$name.smt2" > "/tmp/smtrocq-reader-$name-regenerated.cpc" || exit
  cmp "src/eunoia/tests/fixtures/$name.cpc" "/tmp/smtrocq-reader-$name-regenerated.cpc" || exit
done
```

Build and run the standalone suite through the private toolchain:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 src/eunoia
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 src/eunoia
```

The suite exercises exact AST content, source locations, local/global and lexical
bindings, reused names, scope lifetime, directive policies, malformed syntax,
mutations of actual dumps, and input/depth/node/command bounds. It also asserts
that rule names and `trust` steps are retained for later validation.
