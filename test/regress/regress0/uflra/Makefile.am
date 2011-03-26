TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS = pb_real_10_0100_10_10.smt \
	pb_real_10_0100_10_11.smt \
	pb_real_10_0100_10_15.smt \
	pb_real_10_0100_10_16.smt \
	pb_real_10_0100_10_19.smt \
	pb_real_10_0200_10_22.smt \
	pb_real_10_0200_10_26.smt \
	pb_real_10_0200_10_29.smt
	

# Regression tests for SMT2 inputs
SMT2_TESTS =

# Regression tests for PL inputs
CVC_TESTS = 

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
