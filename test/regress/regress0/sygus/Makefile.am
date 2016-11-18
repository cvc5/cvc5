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
TESTS = commutative.sy \
        constant.sy \
        multi-fun-polynomial2.sy \
        unbdd_inv_gen_winf1.sy \
        max.sy \
        array_sum_2_5.sy \
        parity-AIG-d0.sy \
        twolets1.sy \
        array_search_2.sy \
        hd-01-d1-prog.sy \
        icfp_28_10.sy \
        const-var-test.sy \
        no-syntax-test.sy \
        no-flat-simp.sy \
        twolets2-orig.sy \
        let-ringer.sy \
        let-simp.sy \
        tl-type.sy \
        dup-op.sy \
        nflat-fwd.sy \
        nflat-fwd-3.sy \
        no-syntax-test-bool.sy \
        inv-example.sy \
        uminus_one.sy \
        sygus-dt.sy \
        dt-no-syntax.sy \
        list-head-x.sy \
        clock-inc-tuple.sy \
        dt-test-ns.sy \
        no-mention.sy \
        max2-univ.sy \
        strings-small.sy \
        strings-unconstrained.sy

# sygus tests currently taking too long for make regress
EXTRA_DIST = $(TESTS) \
  max.smt2 \
  sygus-uf.sl \
  enum-test.sy 

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
# error.cvc
#endif

# disabled tests, yet distribute
#EXTRA_DIST += \
# setofsets-disequal.smt2
# no-syntax-test-no-si.sy

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
