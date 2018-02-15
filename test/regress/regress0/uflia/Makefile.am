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
	xs-09-16-3-4-1-5.delta01.smt \
	xs-09-16-3-4-1-5.delta02.smt \
	xs-09-16-3-4-1-5.delta03.smt \
	xs-09-16-3-4-1-5.delta04.smt \
	error1.smt \
	error0.delta01.smt \
	error30.smt

# Regression tests for SMT2 inputs
SMT2_TESTS = \
	check01.smt2 \
	check02.smt2 \
	check03.smt2 \
	check04.smt2 \
	stalmark_e7_27_e7_31.ec.minimized.smt2 \
	tiny.smt2

# Regression tests for PL inputs
CVC_TESTS = 

# Regression tests derived from bug reports
BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

# Necessary to get automake's attention when splitting TESTS into
# SMT_TESTS, SMT2_TESTS, etc..
EXTRA_DIST = $(TESTS) \
	check02.smt2.expect \
	check03.smt2.expect \
	check04.smt2.expect \
	stalmark_e7_27_e7_31.ec.minimized.smt2.expect \
	tiny.smt2.expect

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
