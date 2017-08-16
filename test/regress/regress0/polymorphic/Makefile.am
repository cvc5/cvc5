# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)$(EXEEXT)

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
TESTS =	\
	parsing.smt2 \
	parsing2.smt2 \
	parsing3.smt2 \
	parsing4.smt2 \
	parsing5.smt2 \
	parsing6.smt2 \
	parsing7.smt2 \
	parsing8.smt2 \
	parsing10.smt2 \
	typing_bad1.smt2 \
	typing_bad2.smt2 \
	typing_bad3.smt2 \
	typing_bad4.smt2 \
	typing_bad5.smt2 \
	typing_bad6.smt2 \
	typing_bad7.smt2 \
	typing_bad8.smt2

EXTRA_DIST = $(TESTS)

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif

# disabled tests, yet distribute
#EXTRA_DIST += \
#	parsing9.smt2     #infinite loop
# typing_bad0.smt2  #different debug/prod

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
