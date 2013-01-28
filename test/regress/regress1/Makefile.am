SUBDIRS = . arith

BINARY = cvc4
LOG_COMPILER = @srcdir@/../run_regression
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
TESTS =	bug136.smt \
	bug148.smt \
	friedman_n4_i5.smt \
	hole7.cvc \
	hole8.cvc \
	instance_1444.smt \
	fuzz_2.smt \
	hash_sat_10_09.smt2 \
	hash_sat_07_17.smt2 \
	ooo.tag10.smt2 \
	hash_sat_06_19.smt2 \
	hash_sat_09_09.smt2 \
	ooo.rf6.smt2

EXTRA_DIST = $(TESTS)

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3
regress0 regress2 regress3:
