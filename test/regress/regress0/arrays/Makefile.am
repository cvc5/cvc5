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
TESTS =	\
	arrays0.smt2 \
	arrays1.smt2 \
	arrays2.smt2 \
	arrays3.smt2 \
	arrays4.smt2 \
	incorrect1.smt \
	incorrect2.smt \
	incorrect2.minimized.smt \
	incorrect3.smt \
	incorrect4.smt \
	incorrect5.smt \
	incorrect6.smt \
	incorrect7.smt \
	incorrect8.smt \
	incorrect8.minimized.smt \
	incorrect9.smt \
	incorrect10.smt \
	incorrect11.smt \
	swap_t1_np_nf_ai_00005_007.cvc.smt \
	x2.smt \
	x3.smt \
	bug272.smt \
	bug272.minimized.smt \
	constarr.smt2 \
	constarr2.smt2 \
	constarr3.smt2 \
	constarr.cvc \
	constarr2.cvc \
	constarr3.cvc \
	parsing_ringer.cvc \
	bug637.delta.smt2

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

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
