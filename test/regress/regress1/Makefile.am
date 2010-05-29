TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4
TESTS =	friedman_n4_i5.smt \
	hole7.cvc \
	hole8.cvc \
	instance_1444.smt \
	fuzz_1.smt \
	fuzz_2.smt

# synonyms for "check"
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3
regress0 regress2 regress3:
