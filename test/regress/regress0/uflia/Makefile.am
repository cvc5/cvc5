BINARY = cvc4
if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) --proof @top_builddir@/src/main/$(BINARY)
else
TESTS_ENVIRONMENT = @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS = \
	xs-09-16-3-4-1-5.smt \
	error0.smt2

# Regression tests for SMT2 inputs
SMT2_TESTS = 
#	simplify.javafe.ast.ArrayInit.35_without_quantification2.smt2
#	javafe.ast.StandardPrettyPrint.319_no_forall.smt2 \
#	javafe.ast.WhileStmt.447_no_forall.smt2


# Regression tests for PL inputs
CVC_TESTS = 

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# Necessary to get automake's attention when splitting TESTS into
# SMT_TESTS, SMT2_TESTS, etc..
EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
