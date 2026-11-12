# SMTRocq builds on SMTCoq and consumes a pinned external checker.
all: check-dependencies
	dune build theories

install: check-dependencies
	dune build -p rocq-smtcoq
	dune install rocq-smtcoq

test: check-dependencies
	dune build unit-tests

example: check-dependencies
	dune build examples

benchmark: check-dependencies
	dune build benchmarks

clean:
	dune clean
	find theories src unit-tests examples benchmarks tools -name "_RocqProject" -delete
	rm -f rocq-smtcoq.install

check-dependencies:
	@test -f external/rocq-eunoia-checker/theories/checker/eunoia/EunoiaCertificate.v || \
	  { echo "Initialize the checker: git submodule update --init --recursive" >&2; exit 1; }

.PHONY: all install test example benchmark clean check-dependencies
.NOTPARALLEL:
