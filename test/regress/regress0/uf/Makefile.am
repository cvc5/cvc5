TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/../../bin/cvc4
TESTS =	simple.01.cvc \
	simple.02.cvc \
	simple.03.cvc \
	simple.04.cvc \
	dead_dnd002.smt \
	iso_brn001.smt \
	SEQ032_size2.smt

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
