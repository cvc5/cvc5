# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @abs_top_builddir@/src/main/$(BINARY)$(EXEEXT)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS = \
	constants0.smt \
	simple.01.cvc \
	simple.02.cvc \
	simple.03.cvc \
	simple.04.cvc \
	bug293.cvc \
	bug449.smt \
	pb_real_10_0100_10_10.smt \
	pb_real_10_0100_10_11.smt \
	pb_real_10_0100_10_15.smt \
	pb_real_10_0100_10_16.smt \
	pb_real_10_0100_10_19.smt \
	pb_real_10_0200_10_22.smt \
	pb_real_10_0200_10_26.smt \
	pb_real_10_0200_10_29.smt \
	incorrect1.delta01.smt \
	incorrect1.delta02.smt \
	neq-deltacomp.smt \
	fuzz01.smt

# Regression tests for PL inputs
CVC_TESTS = 

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# Necessary to get automake's attention when splitting TESTS into
# SMT_TESTS, SMT2_TESTS, etc..
EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
