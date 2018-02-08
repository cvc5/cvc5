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
	bug269.smt2 \
	bug290.smt2 \
	bug291.smt2 \
	Arrays_Q1-noinfer.smt2 \
	bug269.smt2 \
	burns13.smt2 \
	burns4.smt2 \
	ex3.smt2 \
	ex6.smt2 \
	set8.smt2 \
	ARI176e1.smt2 \
	bi-artm-s.smt2 \
	simp-typ-test.smt2 \
	macros-int-real.smt2 \
	simp-len.smt2 \
	is-even.smt2 \
	is-even-pred.smt2 \
	delta-simp.smt2  \
	nested-delta.smt2 \
	nested-inf.smt2 \
	RND-small.smt2 \
	clock-3.smt2 \
	cbqi-lia-dt-simp.smt2 \
	is-int.smt2 \
	floor.smt2 \
	mix-simp.smt2 \
	mix-coeff.smt2 \
	mix-match.smt2 \
	ari056.smt2 \
	ext-ex-deq-trigger.smt2 \
	matching-lia-1arg.smt2 \
	agg-rew-test.smt2 \
	agg-rew-test-cf.smt2 \
	rew-to-scala.smt2 \
	macros-real-arg.smt2 \
	anti-sk-simp.smt2 \
	pure_dt_cbqi.smt2 \
	florian-case-ax.smt2 \
	double-pattern.smt2 \
	qcf-rel-dom-opt.smt2 \
	parametric-lists.smt2 \
	partial-trigger.smt2 \
	z3.620661-no-fv-trigger.smt2 \
	bug749-rounding.smt2 \
	RNDPRE_4_1-dd-nqe.smt2 \
	mix-complete-strat.smt2 \
	cbqi-sdlx-fixpoint-3-dd.smt2 \
	qbv-simp.smt2 \
	psyco-001-bv.smt2 \
	qbv-disequality3.smt2 \
	qbv-inequality2.smt2 \
	qbv-test-invert-bvadd-neq.smt2 \
	qbv-test-invert-bvand.smt2 \
	qbv-test-invert-bvand-neq.smt2 \
	qbv-test-invert-bvashr-0.smt2 \
	qbv-test-invert-bvashr-0-neq.smt2 \
	qbv-test-invert-bvashr-1.smt2 \
	qbv-test-invert-bvashr-1-neq.smt2 \
	qbv-test-invert-bvlshr-0.smt2 \
	qbv-test-invert-bvlshr-0-neq.smt2 \
	qbv-test-invert-bvlshr-1.smt2 \
	qbv-test-invert-bvlshr-1-neq.smt2 \
	qbv-test-invert-bvmul.smt2 \
	qbv-test-invert-bvmul-neq.smt2 \
	qbv-test-invert-bvor.smt2 \
	qbv-test-invert-bvor-neq.smt2 \
	qbv-test-invert-bvshl-0.smt2 \
	qbv-test-invert-bvudiv-0-neq.smt2 \
	qbv-test-invert-bvudiv-1-neq.smt2 \
	qbv-test-invert-bvult-1.smt2 \
	qbv-test-invert-bvurem-1-neq.smt2 \
	qbv-test-invert-bvxor.smt2 \
	qbv-test-invert-bvxor-neq.smt2 \
	qbv-test-invert-concat-0.smt2 \
	qbv-test-invert-concat-1.smt2 \
	qbv-test-invert-sign-extend.smt2 \
	qbv-test-urem-rewrite.smt2 \
	extract-nproc.smt2 \
	clock-10.smt2 \
	lra-triv-gn.smt2
 

# regression can be solved with --finite-model-find --fmf-inst-engine
# set3.smt2

# FIXME: I've disabled these since they give different error messages on production and debug
#	macro-subtype-param.smt2 
#	subtype-param-unk.smt2 
#	subtype-param.smt2 

EXTRA_DIST = $(TESTS) \
	bug291.smt2.expect

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
