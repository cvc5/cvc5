SUBDIRS = boolean arith . 

BINARY = cvc4
LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)$(EXEEXT)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(TESTS_ENVIRONMENT) $(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
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

BUG_TESTS = \
	bug216.smt2 \
	bug233.cvc \
	bug326.smt2 \
	arith_lra_01.smt2 \
	arith_lra_02.smt2

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	bug216.smt2.expect \
	bug396.smt2 \
	bug394.smt2

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
