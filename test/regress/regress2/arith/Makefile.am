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

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	abz5_1400.smt \
	pursuit-safety-11.smt \
	pursuit-safety-12.smt \
	sc-7.base.cvc.smt \
	uart-8.base.cvc.smt \
	qlock-4-10-9.base.cvc.smt2 \
	lpsat-goal-9.smt2 \
	prp-13-24.smt2


EXTRA_DIST = $(TESTS) \
	miplib-opt1217--27.smt2 \
	miplib-pp08a-3000.smt2 \
	arith-int-098.cvc

# synonyms for "check" in this directory
.PHONY: regress regress2 test
regress regress2 test: check

# do nothing in this subdir
.PHONY: regress0 regress1 regress3 regress4
regress0 regress1 regress3 regress4:
