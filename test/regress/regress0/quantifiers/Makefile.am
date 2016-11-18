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
	bignum_quant.smt2 \
	bug269.smt2 \
	burns13.smt2 \
	burns4.smt2 \
	ex3.smt2 \
	ex6.smt2 \
	opisavailable-12.smt2 \
	ricart-agrawala6.smt2 \
	set8.smt2 \
	smtlib384a03.smt2 \
	smtlib46f14a.smt2 \
	smtlibf957ea.smt2 \
	gauss_init_0030.fof.smt2 \
	qcft-javafe.filespace.TreeWalker.006.smt2 \
	qcft-smtlib3dbc51.smt2 \
	javafe.ast.StmtVec.009.smt2 \
	ARI176e1.smt2 \
	bi-artm-s.smt2 \
	simp-typ-test.smt2 \
	macros-int-real.smt2 \
	stream-x2014-09-18-unsat.smt2 \
	simp-len.smt2 \
	is-even.smt2 \
	is-even-pred.smt2 \
	delta-simp.smt2  \
	nested-delta.smt2 \
	nested-inf.smt2 \
	RND-small.smt2 \
	clock-3.smt2 \
	006-cbqi-ite.smt2 \
	cbqi-lia-dt-simp.smt2 \
	is-int.smt2 \
	floor.smt2 \
	array-unsat-simp3.smt2 \
	mix-simp.smt2 \
	mix-coeff.smt2 \
	mix-match.smt2 \
	ari056.smt2 \
	ext-ex-deq-trigger.smt2 \
	matching-lia-1arg.smt2 \
	RND_4_16.smt2 \
	cdt-0208-to.smt2 \
	psyco-196.smt2 \
	agg-rew-test.smt2 \
	agg-rew-test-cf.smt2 \
	rew-to-0211-dd.smt2 \
	rew-to-scala.smt2 \
	macro-subtype-param.smt2 \
	macros-real-arg.smt2 \
	subtype-param-unk.smt2 \
	subtype-param.smt2 \
	anti-sk-simp.smt2 \
	pure_dt_cbqi.smt2 \
	florian-case-ax.smt2 \
	double-pattern.smt2 \
	qcf-rel-dom-opt.smt2 \
	parametric-lists.smt2 \
	partial-trigger.smt2 \
	inst-max-level-segf.smt2 \
	small-bug1-fixpoint-3.smt2 \
	z3.620661-no-fv-trigger.smt2 \
	bug_743.smt2 \
	quaternion_ds1_symm_0428.fof.smt2 \
	bug749-rounding.smt2 \
	RNDPRE_4_1-dd-nqe.smt2 \
	mix-complete-strat.smt2


# regression can be solved with --finite-model-find --fmf-inst-engine
# set3.smt2


# removed because they take more than 20s
#		javafe.ast.ArrayInit.35.smt2 \
#		javafe.ast.StandardPrettyPrint.319.smt2 \
#		javafe.ast.StmtVec.009.smt2 \
#		javafe.ast.WhileStmt.447.smt2 \
#		javafe.tc.CheckCompilationUnit.001.smt2 \
#		javafe.tc.FlowInsensitiveChecks.682.smt2 \
#		clock-10.smt2
#

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
