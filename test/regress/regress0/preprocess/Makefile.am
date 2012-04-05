SUBDIRS = . 

if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) --proof @top_builddir@/src/main/cvc4
else
TESTS_ENVIRONMENT = @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/cvc4
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS =

# Regression tests for SMT2 inputs
SMT2_TESTS =

# Regression tests for PL inputs
CVC_TESTS = \
	preprocess_00.cvc \
	preprocess_01.cvc \
	preprocess_02.cvc \
	preprocess_03.cvc \
	preprocess_04.cvc \
	preprocess_05.cvc \
	preprocess_06.cvc \
	preprocess_07.cvc \
	preprocess_08.cvc \
	preprocess_09.cvc \
	preprocess_10.cvc \
	preprocess_11.cvc \
	preprocess_12.cvc

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
