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
	array_sum_dd.sy \
	icfp_easy_mt_ite.sy \
	inv_gen_n_c11.sy \
	MPwL_d1s3.sy \
	nia-max-square.sy \
	no-syntax-test-no-si.sy \
	process-10-vars-2fun.sy \
	process-arg-invariance.sy \
	real-grammar-neg.sy \
	lustre-real.sy \
	max2-univ.sy \
	mpg_guard1-dd.sy \
	three.sy

EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress2 test
regress regress2 test: check

# do nothing in this subdir
.PHONY: regress0 regress1 regress3 regress4
regress0 regress1 regress3 regress4:
