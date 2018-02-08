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
	array_card.smt2 \
	german169.smt2 \
	QEpres-uf.855035.smt \
	agree467.smt2 \
	Arrow_Order-smtlib.778341.smt \
	german73.smt2 \
	PUZ001+1.smt2 \
	refcount24.cvc.smt2 \
	fmf-bound-int.smt2 \
	fc-simple.smt2 \
	fc-unsat-tot-2.smt2 \
	fc-unsat-pent.smt2 \
	Hoare-z3.931718.smt \
	fore19-exp2-core.smt2 \
	syn002-si-real-int.smt2 \
	krs-sat.smt2 \
	forall_unit_data2.smt2 \
	sc_bad_model_1221.smt2 \
 	dt-proper-model.smt2 \
	fd-false.smt2 \
	tail_rec.smt2 \
	loopy_coda.smt2 \
	fmc_unsound_model.smt2 \
	am-bad-model.cvc \
	sc-crash-052316.smt2 \
	bound-int-alt.smt2 \
	bug723-irrelevant-funs.smt2 \
	bounded_sets.smt2 \
	fmf-strange-bounds-2.smt2 \
	memory_model-R_cpp-dd.cvc \
	ko-bound-set.cvc \
	cons-sets-bounds.smt2 \
	bug651.smt2 \
	bug652.smt2 \
	bug782.smt2 \
	quant_real_univ.cvc \
	constr-ground-to.smt2 \
	bug-041417-set-options.cvc \
	alg202+1.smt2 \
	fmf-fun-no-elim-ext-arith.smt2 \
	cruanes-no-minimal-unk.smt2 \
	no-minimal-sat.smt2 \
	sat-logic.smt2 

EXTRA_DIST = $(TESTS)


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
