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
	arith_lra_01.smt2 \
	arith_lra_02.smt2 \
	bug-fmf-fun-skolem.smt2 \
	bug216.smt2 \
	bug326.smt2 \
	fuzz_1_to_52_merged.smt2 \
	fuzz_1.smt2 \
	fuzz_10.smt2 \
	fuzz_11.smt2 \
	fuzz_15.smt2 \
	fuzz_16.smt2 \
	fuzz_19.smt2 \
	fuzz_20.smt2 \
	fuzz_23.smt2 \
	fuzz_24.smt2 \
	fuzz_25.smt2 \
	fuzz_26.smt2 \
	fuzz_28.smt2 \
	fuzz_29.smt2 \
	fuzz_3_1.smt2 \
	fuzz_3_10.smt2 \
	fuzz_3_11.smt2 \
	fuzz_3_12.smt2 \
	fuzz_3_13.smt2 \
	fuzz_3_14.smt2 \
	fuzz_3_15.smt2 \
	fuzz_3_2.smt2 \
	fuzz_3_3.smt2 \
	fuzz_3_4.smt2 \
	fuzz_3_5.smt2 \
	fuzz_3_6.smt2 \
	fuzz_3_7.smt2 \
	fuzz_3_8.smt2 \
	fuzz_3_9.smt2 \
	fuzz_30.smt2 \
	fuzz_32.smt2 \
	fuzz_34.smt2 \
	fuzz_35.smt2 \
	fuzz_37.smt2 \
	fuzz_39.smt2 \
	fuzz_4.smt2 \
	fuzz_40.smt2 \
	fuzz_41.smt2 \
	fuzz_42.smt2 \
	fuzz_43.smt2 \
	fuzz_44.smt2 \
	fuzz_45.smt2 \
	fuzz_5_1.smt2 \
	fuzz_5_2.smt2 \
	fuzz_5_3.smt2 \
	fuzz_5_4.smt2 \
	fuzz_5_5.smt2 \
	fuzz_5_6.smt2 \
	fuzz_5.smt2 \
	fuzz_51.smt2 \
	fuzz_52.smt2 \
	fuzz_6.smt2 \
	fuzz_7.smt2 \
	fuzz_8.smt2 \
	fuzz_9.smt2 \
	quant-fun-proc-unmacro.smt2 \
	quant-fun-proc.smt2
	
EXTRA_DIST = $(TESTS) \
	bug216.smt2.expect

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
