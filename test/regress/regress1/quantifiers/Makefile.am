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
	bug802.smt2 \
	006-cbqi-ite.smt2 \
	REM \
	AdditiveMethods_OwnedResults.Mz.smt2 \
	ari118-bv-2occ-x.smt2 \
	array-unsat-simp3.smt2 \
	bignum_quant.smt2 \
	bug_743.smt2 \
	bug822.smt2 \
	cdt-0208-to.smt2 \
	gauss_init_0030.fof.smt2 \
	inst-max-level-segf.smt2 \
	intersection-example-onelane.proof-node22337.smt2 \
	javafe.ast.StmtVec.009.smt2 \
	model_6_1_bv.smt2 \
	nested9_true-unreach-call.i_575.smt2 \
	NUM878.smt2 \
	opisavailable-12.smt2 \
	psyco-107-bv.smt2 \
	psyco-196.smt2 \
	qbv-simple-2vars-vo.smt2 \
	qbv-test-invert-bvcomp.smt2 \
	qbv-test-invert-bvudiv-0.smt2 \
	qbv-test-invert-bvudiv-1.smt2 \
	qbv-test-invert-bvurem-1.smt2 \
	qcft-javafe.filespace.TreeWalker.006.smt2 \
	qcft-smtlib3dbc51.smt2 \
	quaternion_ds1_symm_0428.fof.smt2 \
	rew-to-0211-dd.smt2 \
	ricart-agrawala6.smt2 \
	RND_4_16.smt2 \
	small-pipeline-fixpoint-3.smt2 \
	smtlib384a03.smt2 \
	smtlib46f14a.smt2 \
	smtlibf957ea.smt2 \
	stream-x2014-09-18-unsat.smt2 \
	symmetric_unsat_7.smt2


EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
