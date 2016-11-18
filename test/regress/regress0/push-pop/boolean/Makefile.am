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
	fuzz_1.smt2 \
	fuzz_2.smt2 \
	fuzz_3.smt2 \
	fuzz_4.smt2 \
	fuzz_5.smt2 \
	fuzz_6.smt2 \
	fuzz_7.smt2 \
	fuzz_8.smt2 \
	fuzz_9.smt2 \
	fuzz_10.smt2 \
	fuzz_11.smt2 \
	fuzz_12.smt2 \
	fuzz_13.smt2 \
	fuzz_14.smt2 \
	fuzz_15.smt2 \
	fuzz_16.smt2 \
	fuzz_18.smt2 \
	fuzz_19.smt2 \
	fuzz_20.smt2 \
	fuzz_21.smt2 \
	fuzz_22.smt2 \
	fuzz_23.smt2 \
	fuzz_24.smt2 \
	fuzz_25.smt2 \
	fuzz_26.smt2 \
	fuzz_27.smt2 \
	fuzz_28.smt2 \
	fuzz_29.smt2 \
	fuzz_30.smt2 \
	fuzz_31.smt2 \
	fuzz_32.smt2 \
	fuzz_33.smt2 \
	fuzz_34.smt2 \
	fuzz_35.smt2 \
	fuzz_36.smt2 \
	fuzz_37.smt2 \
	fuzz_38.smt2 \
	fuzz_39.smt2 \
	fuzz_40.smt2 \
	fuzz_41.smt2 \
	fuzz_42.smt2 \
	fuzz_43.smt2 \
	fuzz_44.smt2 \
	fuzz_45.smt2 \
	fuzz_46.smt2 \
	fuzz_47.smt2 \
	fuzz_48.smt2 \
	fuzz_49.smt2 \
	fuzz_50.smt2 \
	fuzz_51.smt2 \
	fuzz_52.smt2 

# Disabled because they take too long
#	fuzz_1_to_52_merged.smt2 \
#

BUG_TESTS = 

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) 

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
