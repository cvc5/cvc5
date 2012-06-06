SUBDIRS = . core

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
	fuzz01.smt \
	fuzz02.smt \
	fuzz03.smt \
	fuzz04.smt \
	fuzz05.smt \
	fuzz06.smt \
	fuzz07.smt \
	fuzz08.smt \
	fuzz09.smt \
	fuzz10.smt \
	fuzz11.smt \
	fuzz12.smt \
	fuzz13.smt \
	fuzz14.smt \
	calc2_sec2_shifter_mult_bmc15.atlas.delta01.smt

# Regression tests for SMT2 inputs
SMT2_TESTS =

# Regression tests for PL inputs
CVC_TESTS = bvsimple.cvc

# Regression tests derived from bug reports
BUG_TESTS = \
	bug260a.smt \
	bug260b.smt

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	test00.smt \
	bvcomp.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
