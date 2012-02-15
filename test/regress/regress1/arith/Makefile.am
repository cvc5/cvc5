if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../../run_regression --proof @top_builddir@/src/main/cvc4
else
TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4
endif

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	abz5_1400.smt \
	pursuit-safety-11.smt \
	pursuit-safety-12.smt \
	sc-7.base.cvc.smt \
	uart-8.base.cvc.smt \
	qlock-4-10-9.base.cvc.smt2 \
	lpsat-goal-9.smt2

EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3
regress0 regress2 regress3:
