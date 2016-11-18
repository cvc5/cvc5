SUBDIRS = . 

# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../../run_regression
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
CVC_TESTS =

SMT2_TESTS = \
	fuzz_3_10.smt2 \
	fuzz_3_11.smt2 \
	fuzz_3_12.smt2 \
	fuzz_3_13.smt2 \
	fuzz_3_14.smt2 \
	fuzz_3_15.smt2 \
	fuzz_3_1.smt2 \
	fuzz_3_2.smt2 \
	fuzz_3_3.smt2 \
	fuzz_3_4.smt2 \
	fuzz_3_5.smt2 \
	fuzz_3_6.smt2 \
	fuzz_3_7.smt2 \
	fuzz_3_8.smt2 \
	fuzz_3_9.smt2 \
	fuzz_5_1.smt2 \
	fuzz_5_2.smt2 \
	fuzz_5_3.smt2 \
	fuzz_5_4.smt2 \
	fuzz_5_5.smt2 \
	fuzz_5_6.smt2

BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) 

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
