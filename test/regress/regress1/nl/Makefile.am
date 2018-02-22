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
	mirko-050417.smt2 \
	arrowsmith-050317.smt2 \
	bug698.smt2 \
	dist-big.smt2 \
	dumortier_llibre_artes_ex_5_13.transcendental.k2.smt2 \
	exp-4.5-lt.smt2 \
	metitarski_3_4_2e.smt2 \
	metitarski-3-4.smt2 \
	nl-help-unsat-quant.smt2 \
	poly-1025.smt2 \
	quant-nl.smt2 \
	red-exp.smt2 \
	rewriting-sums.smt2 \
	simple-mono.smt2 \
	sin1-sat.smt2 \
	sin-compare.smt2 \
	sin-compare-across-phase.smt2 \
	sqrt-problem-1.smt2 \
	sugar-ident-2.smt2 \
	sugar-ident-3.smt2 \
	tan-rewrite2.smt2 \
	bad-050217.smt2 \
	coeff-unsat-base.smt2 \
	coeff-unsat.smt2 \
	combine.smt2 \
	cos-bound.smt2 \
	cos1-tc.smt2 \
	disj-eval.smt2 \
	div-mod-partial.smt2 \
	exp_monotone.smt2 \
	exp1-lb.smt2 \
	metitarski-1025.smt2 \
	NAVIGATION2.smt2 \
	nl-unk-quant.smt2 \
	ones.smt2 \
	shifting.smt2 \
	shifting2.smt2 \
	simple-mono-unsat.smt2 \
	sin-init-tangents.smt2 \
	sin-sign.smt2 \
	sin-sym2.smt2 \
	sin1-lb.smt2 \
	sin1-ub.smt2 \
	sin2-lb.smt2 \
	sin2-ub.smt2 \
	sugar-ident.smt2 \
	zero-subset.smt2 \
	sin1-deq-sat.smt2

EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
