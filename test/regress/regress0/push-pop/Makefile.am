SUBDIRS = . 

BINARY = cvc4
if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../../run_regression --proof @top_builddir@/src/main/$(BINARY)
else
TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/$(BINARY)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
CVC_TESTS = \
	test.00.cvc \
	test.01.cvc \
	units.cvc \
	incremental-subst-bug.cvc

SMT2_TESTS = \
	tiny_bug.smt2

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) 

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
