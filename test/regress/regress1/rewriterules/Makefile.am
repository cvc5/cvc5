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

override CVC4_REGRESSION_ARGS += --rewrite-rules
export CVC4_REGRESSION_ARGS

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	reachability_back_to_the_future.smt2 \
	read5.smt2 \
	length_gen.smt2 \
	length_gen_020.smt2 \
	length_gen_020_sat.smt2 \
	length_gen_040.smt2 \
	length_gen_040_lemma.smt2 \
	length_gen_040_lemma_trigger.smt2 \
	datatypes_sat.smt2


EXTRA_DIST = $(TESTS) \
	datatypes_clark_quantification.smt2 \
	datatypes2.smt2 \
	datatypes3.smt2 \
	length_gen_010_lemma.smt2 \
	length_gen_010.smt2 \
	length_gen_080.smt2 \
	length_gen_160_lemma.smt2 \
	length_gen_inv_160.smt2 \
	length_trick3_int.smt2 \
	length_trick3.smt2 \
	set_A_new_fast_tableau-base_sat.smt2 \
	set_A_new_fast_tableau-base.smt2 \
	test_guards.smt2 \
	why3_vstte10_max_sum_harness2.smt2

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
