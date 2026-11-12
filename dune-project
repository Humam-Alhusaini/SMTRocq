(lang dune 3.21)

(using rocq 0.11)

(name rocq-smtcoq)

(generate_opam_files)

(source
 (github Humam-Alhusaini/SMTRocq))

(license CECILL-C)

(authors
 "Michaël Armand"
 "Valentin Blot"
 "Amina Bousalem"
 "Quentin Garchery"
 "Benjamin Grégoire"
 "Chantal Keller"
 "Burak Ekici"
 "Alain Mebsout")

(maintainers "Humam-Alhusaini")

(package
 ; Main project
 (name rocq-smtcoq)
 (synopsis "SMTRocq: a CVC5-backed SMT tactic built on SMTCoq")
 (description
  "SMTRocq builds upon SMTCoq's verified theory semantics, reflective proof checkers, and Rocq preprocessing. It adds a CVC5 backend that translates untrusted solver proofs into compact checked certificates. The Eunoia/CPC checker is maintained separately in rocq-eunoia-checker and consumed as a pinned source dependency. Existing SMTCoq logical names are retained for compatibility.")
 (tags
  ("category:Computer Science/Decision Procedures and Certified Algorithms/Decision procedures"
   "category:Miscellaneous/Coq Extensions"
   "keyword: SMT"
   "keyword: SAT"
   "keyword: automation"
   "logpath:SMTCoq"))
 (depends
  conf-python-3
  num
  (rocq-core
   (>= 9.2.0))
  rocq-stdlib
  rocq-trakt))
