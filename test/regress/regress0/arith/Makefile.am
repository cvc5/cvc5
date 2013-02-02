SUBDIRS = . integers

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
TESTS =	\
	arith.01.cvc \
	arith.02.cvc \
	arith.03.cvc \
	delta-minimized-row-vector-bug.smt \
	fuzz_3-eq.smt \
	leq.01.smt \
	miplibtrick.smt \
	DTP_k2_n35_c175_s15.smt2 \
	mod.01.smt2 \
	mod.02.smt2 \
	mod.03.smt2 \
	div.01.smt2 \
	div.02.smt2 \
	div.03.smt2 \
	div.04.smt2 \
	div.05.smt2 \
	div.06.smt2 \
	div.07.smt2 \
	div.08.smt2 \
	div.09.smt2 \
	mult.01.smt2 \
	mult.02.smt2 \
	bug443.delta01.smt
#	problem__003.smt2

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
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
