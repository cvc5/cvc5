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
	bv-proof00.smt \
	fuzz34.smt \
	fuzz38.smt \
	bug_extract_mult_leading_bit.smt2 \
	bug787.smt2 \
	bv-int-collapse2-sat.smt2 \
	cmu-rdk-3.smt2 \
	decision-weight00.smt2 \
	divtest.smt2 \
	bv2nat-ground.smt2 \
	bv2nat-simp-range-sat.smt2 \
	unsound1.smt2

EXTRA_DIST = $(TESTS)

# This benchmark is currently disabled as it uses --check-proof
# bench_38.delta.smt2

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
