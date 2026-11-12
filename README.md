# SMTCoq

## Presentation
SMTCoq is a [Rocq](http://rocq-prover.org) plugin that checks proof witnesses coming from external SAT and SMT solvers. It provides:
* a certified checker for proof witnesses coming from the SAT solver [ZChaff](https://www.princeton.edu/~chaff/zchaff.html) and the SMT solvers [veriT](https://www.verit-solver.org/) and [CVC4](https://cvc4.github.io/). This checker increases the confidence in these tools by checking their answers a posteriori and allows to import new theroems proved by these solvers in Rocq;
* decision procedures through new tactics that discharge some Coq goals to ZChaff, veriT, CVC4, and their combination.
* abducts for goals that external solvers fail to prove, which represent possibly missing hypotheses that would allow them to prove the goal, using the cvc5 SMT solver.

If you are looking for powerful automated tactics that use SMT solvers, you can look at the [Sniper](https://github.com/smtcoq/sniper) plugin, which uses SMTCoq as a backend.

## Installation and use
SMTCoq is freely available as an [opam package](https://rocq-prover.org/p/coq-smtcoq/latest) and on [GitHub](https://github.com/smtcoq/smtcoq). See the [INSTALL.md](INSTALL.md) file for instructions on how to install SMTCoq and the supported provers.

See [the examples](https://github.com/smtcoq/smtcoq/blob/main/examples/Example.v) to see how to use SMTCoq. More details are given in the [USE.md](https://github.com/smtcoq/smtcoq/blob/main/USE.md) file.

SMTCoq is distributed under the CeCILL-C license.

## Development cvc5 / Eunoia backend

The new `smtrocq` tactic compiles CVC5 Eunoia proofs into compact certificates
checked by verified SMTCoq operations. Use the lean entry point:

```coq
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Goal forall x y : Z, x <= y -> y < x + 1 -> x = y.
Proof. smtrocq. Qed.
```

See the [tactic guide](docs/eunoia/smtrocq-tactic-2026-11-11.md) for coverage,
the checking contract and validation. `smtrocq` proves the actual theorem;
`cvc5_eunoia` also validates the CPC source derivation. Both use the existing
SMTCoq semantics and retain kernel-checked proof construction.

The frozen comparison measures 38% less tactic-plus-`Qed` time than `verit` on
the standard UF/LIA suite, and about 2× faster proof construction on shared
scaling cases.
Fresh whole-compiler processes remain about 5% slower. The guide retains all
coverage failures and the exact timing boundaries.

`cvc5_eunoia` invokes the pinned private cvc5 1.4.2 installation, computes its
CPC proof rules from the Eunoia signature, and checks every inference using
SMTCoq's existing semantics and reflective checkers. For example:

```coq
From SMTCoq Require Import SMTCoq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Lemma cvc5_congruence :
  forall (A : Type) (HA : CompDec A) (f : A -> A) (x y : A),
    x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.

Lemma cvc5_bounds (x : Z) : x <= 0 -> x >= 1 -> False.
Proof. cvc5_eunoia. Qed.
```

The current fragment covers tested UF and integer arithmetic goals, including
[proved facts for Rocq division/modulo by constants](docs/eunoia/division.md); unsupported
source rules and exhausted certificate search reject. Broader coverage and
performance work are in progress. See the [backend guide](docs/eunoia/README.md),
[implementation status](docs/eunoia/implementation-plan.md),
[private solver setup and provenance](scripts/eunoia/README.md),
[signature regeneration](tools/eunoia/README.md), and
[checked benchmark protocol](benchmarks/eunoia/README.md).
The [direct Boolean front end](docs/eunoia/boolean-frontend-2026-11-09.md) builds
checked reflection proofs and retains the existing preprocessing as a fallback.
For the strict CPC tactic, it reduces a 64-link equality-chain diagnostic from 24.9 s to 4.6 s and improves
the standard proof-construction workload by about 8%; veriT parity remains open.

The earlier [integer-map comparison fix](docs/eunoia/opaque-array-comparison-2026-11-09.md)
removes repeated arithmetic-proof evaluation from both checkers. It substantially
reduces strict CPC proof-construction time; that LIA path still trails veriT. Earlier
[proof-construction measurements](docs/eunoia/construction-bundle.md) retain their
own checkpoints and timing boundaries.
The [proof-specific compilation experiment](docs/eunoia/specialized-rules.md)
generates individually checked rule implementations and remains off by default.

## Example
Here is a very small example of the possibilities of SMTCoq: automatic proofs in group theory.

```coq
From SMTCoq Require Import SMTCoq.
From Stdlib Require Import ZArith.

Local Open Scope Z_scope.

Section group.
  Variable e : Z.
  Variable inv : Z -> Z.
  Variable op : Z -> Z -> Z.

  Hypothesis associative :
    forall a b c, op a (op b c) =? op (op a b) c.
  Hypothesis identity : forall a, (op e a =? a).
  Hypothesis inverse : forall a, (op (inv a) a =? e).

  Add_lemmas associative identity inverse.

  Lemma inverse' :
    forall a : Z, (op a (inv a) =? e).
  Proof. smt. Qed.

  Lemma identity' :
    forall a : Z, (op a e =? a).
  Proof. smt inverse'. Qed.

  Lemma unique_identity e':
    (forall z, op e' z =? z) -> e' =? e.
  Proof. intros pe'; smt pe'. Qed.

  Clear_lemmas.
End group.
```

## Want to participate?

SMTCoq is an ambitious, collaborative project: everyone is welcome!
There are many and varied enhancement to do: join the [SMTCoq
forum](https://framateam.org/smtcoq) to discuss!

## People
### Current team
* [Clark Barrett](http://www.cs.nyu.edu/~barrett) (Stanford University)
* [Valentin Blot](https://valentinblot.org/pro) (Inria)
* Amina Bousalem (Université Paris-Sud)
* [Louise Dubois de Prisque](https://louiseddp.github.io) (Inria)
* [Burak Ekici](http://ekiciburak.github.io/) (The University of Iowa)
* Quentin Garchery (Université Paris-Sud, Inria)
* [Benjamin Grégoire](https://www-sop.inria.fr/members/Benjamin.Gregoire/) (Inria Sophia Antipolis)
* [Guy Katz](http://stanford.edu/~guyk) (Stanford University)
* [Chantal Keller](https://usr.lmf.cnrs.fr/~ckeller/index-en.html) (Université Paris-Saclay)
* [Vincent Lafeychine](https://lafeychine.codeberg.page/) (Université Paris-Saclay)
* [Alain Mebsout](https://mebsout.github.io/) (OcamlPro)
* [Andrew Reynolds](http://homepage.divms.uiowa.edu/~ajreynol) (The University of Iowa)
* [Laurent Théry](https://www-sop.inria.fr/marelle/Laurent.Thery/moi.html) (Inria Sophia Antipolis)
* [Cesare Tinelli](http://homepage.cs.uiowa.edu/~tinelli/) (The University of Iowa)
* [Pierre Vial](https://pierrevial.github.io) (Formal Land)

### Past contributors
* Mikaël Armand (Inria Sophia Antipolis)
* Germain Faure (Inria Saclay)
* Tianyi Liang (The University of Iowa)
* [Benjamin Werner](http://www.lix.polytechnique.fr/Labo/Benjamin.Werner) (École polytechnique)


## Publications
### Reference
[A Modular Integration of SAT/SMT Solvers to Coq through Proof Witnesses](http://hal.inria.fr/docs/00/63/91/30/PDF/cpp11.pdf), Armand, Michaël; Faure, Germain; Grégoire, Benjamin; Keller, Chantal; Thery, Laurent; Werner, Benjamin, [CPP - Certified Programs and Proofs - First International Conference - 2011](http://formes.asia/cpp).

### Other publications
1. [SMTCoq: A plug-in for integrating SMT solvers into Coq (Tool Paper)](http://homepage.divms.uiowa.edu/~tinelli/papers/EkiEtAl-CAV-17.pdf), Ekici, Burak; Mebsout, Alain; Tinelli, Cesare; Keller, Chantal; Katz, Guy; Reynolds, Andrew; Barrett, Clark, [CAV - International Conference on Computer Aided Verification](http://cavconference.org/2017) - 2017.
2. [Extending SMTCoq, a Certified Checker for SMT (Extended Abstract)](https://hal.inria.fr/hal-01388984/document), Ekici, Burak; Katz, Guy; Keller, Chantal; Mebsout, Alain; Reynolds, Andrew; Tinelli, Cesare, [HaTT - on Hammers for Type Theories - First International Workshop](https://hatt2016.inria.fr) - 2016.
3. [Verifying SAT and SMT in Coq for a fully automated decision procedure](http://hal.inria.fr/docs/00/61/40/41/PDF/ArmandAl.pdf), Armand, Mickaël; Faure, Germain; Grégoire, Benjamin; Keller, Chantal; Théry, Laurent; Wener, Benjamin, [PSATTT - International Workshop on Proof-Search in Axiomatic Theories and Type Theories](http://www.lix.polytechnique.fr/~lengrand/Events/PSATTT11) - 2011.
4. SMTCoq : automatisation expressive et extensible dans Coq, Blot, Valentin; Bousalem, Amina; Garchery, Quentin; Keller, Chantal, [JFLA - Journées Francophones des Langages Applicatifs](http://dpt-info.u-strasbg.fr/~magaud/JFLA2019) - 2019.
