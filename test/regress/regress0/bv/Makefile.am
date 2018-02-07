SUBDIRS = . core

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

# FIXME: Proof checking takes too long. Add this back.
# 	fuzz15.delta01.smt 

# Regression tests for SMT inputs
SMT_TESTS = \
	fuzz01.smt \
	fuzz02.delta01.smt \
	fuzz02.smt \
	fuzz03.smt \
	fuzz04.smt \
	fuzz05.smt \
	fuzz06.smt \
	fuzz07.smt \
	fuzz08.smt \
	fuzz09.smt \
	fuzz10.smt \
	fuzz11.smt \
	fuzz12.smt \
	fuzz13.smt \
	fuzz14.smt \
	fuzz16.delta01.smt \
	fuzz17.delta01.smt \
	fuzz18.delta01.smt \
	fuzz18.delta02.smt \
	fuzz18.delta03.smt \
	fuzz18.smt \
	fuzz19.delta01.smt \
	fuzz19.smt \
	fuzz20.delta01.smt \
	fuzz20.smt \
	fuzz21.delta01.smt \
	fuzz21.smt \
	fuzz22.delta01.smt \
	fuzz22.smt \
	fuzz23.delta01.smt \
	fuzz23.smt \
	fuzz24.delta01.smt \
	fuzz24.smt \
	fuzz25.delta01.smt \
	fuzz25.smt \
	fuzz26.delta01.smt \
	fuzz26.smt \
	fuzz27.delta01.smt \
	fuzz27.smt \
	fuzz28.delta01.smt \
	fuzz28.smt \
	fuzz29.delta01.smt \
	fuzz29.smt \
	fuzz30.delta01.smt \
	fuzz30.smt \
	fuzz31.delta01.smt \
	fuzz31.smt \
	fuzz32.delta01.smt \
	fuzz32.smt \
	fuzz33.delta01.smt \
	fuzz33.smt \
	fuzz34.delta01.smt \
	fuzz35.delta01.smt \
	fuzz35.smt \
	fuzz36.delta01.smt \
	fuzz36.smt \
	fuzz37.delta01.smt \
	fuzz37.smt \
	fuzz38.delta01.smt \
	fuzz39.delta01.smt \
	fuzz39.smt \
	fuzz40.delta01.smt \
	fuzz40.smt \
	fuzz41.smt \
	calc2_sec2_shifter_mult_bmc15.atlas.delta01.smt \
	smtcompbug.smt \
	unsound1.smt2 \
	unsound1-reduced.smt2 \
	bv2nat-ground.smt2 \
	bv2nat-ground-c.smt2 \
	cmu-rdk-3.smt2 \
	bv2nat-simp-range.smt2 \
	bv2nat-simp-range-sat.smt2 \
	bv-int-collapse1.smt2 \
	bv-int-collapse2.smt2 \
	bv-int-collapse2-sat.smt2 \
	divtest_2_5.smt2 \
	divtest_2_6.smt2 \
	mul-neg-unsat.smt2 \
	mul-negpow2.smt2 \
	bvmul-pow2-only.smt2

# This benchmark is currently disabled as it uses --check-proof
# bench_38.delta.smt2

# Regression tests for SMT2 inputs
SMT2_TESTS = divtest.smt2

# Regression tests for PL inputs
CVC_TESTS = bvsimple.cvc sizecheck.cvc

# Regression tests derived from bug reports
BUG_TESTS = \
	bug260a.smt \
	bug260b.smt \
	bug440.smt \
	bug733.smt2 \
	bug734.smt2 \
	bug_extract_mult_leading_bit.smt2 \
	bug787.smt2

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	test00.smt \
	bvcomp.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
