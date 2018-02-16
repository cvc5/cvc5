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
TESTS = \
	FIREFLY_luke_1b_e2_3049_e7_1173.ec.minimized.smt2 \
	microwave21.ec.minimized.smt2 \
	simple_cyclic2.smt2 \
	DRAGON_11_e1_2450.ec.minimized.smt2 \
	FIREFLY_3_e2_2236_e7_3681.ec.core.smt2 \
	speed2_e8_449_e8_517.ec.smt2 \
	stalmark_e7_27_e7_31.ec.smt2


EXTRA_DIST = $(TESTS) \
	DRAGON_11_e1_2450.ec.minimized.smt2.expect \
	FIREFLY_3_e2_2236_e7_3681.ec.core.smt2.expect \
	speed2_e8_449_e8_517.ec.smt2.expect \
	stalmark_e7_27_e7_31.ec.smt2.expect

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
