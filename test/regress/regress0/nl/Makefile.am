SUBDIRS = .

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
  quant-nl.smt2 \
  dist-big.smt2 \
  simple-mono.smt2 \
  coeff-sat.smt2 \
  combine.smt2 \
  magnitude-wrong-1020-m.smt2 \
  nl-unk-quant.smt2 \
  mult-po.smt2 \
  very-simple-unsat.smt2 \
  subs0-unsat-confirm.smt2 \
  simple-mono-unsat.smt2 \
  ones.smt2 \
  metitarski_3_4_2e.smt2 \
  metitarski-1025.smt2 \
  poly-1025.smt2 \
  very-easy-sat.smt2 \
  coeff-unsat.smt2 \
  coeff-unsat-base.smt2 \
  red-exp.smt2 \
  zero-subset.smt2 \
  nia-wrong-tl.smt2 \
  nl-help-unsat-quant.smt2 \
  metitarski-3-4.smt2 \
  rewriting-sums.smt2 \
  disj-eval.smt2 \
  bug698.smt2  \
  real-div-ufnra.smt2 \
  div-mod-partial.smt2 \
  all-logic.smt2 \
  sqrt-problem-1.smt2 \
  real-as-int.smt2 \
  nta/bad-050217.smt2 \
  nta/cos-bound.smt2 \
  nta/cos-sig-value.smt2 \
  nta/exp_monotone.smt2 \
  nta/shifting2.smt2 \
  nta/shifting.smt2 \
  nta/sin-compare-across-phase.smt2 \
  nta/sin-compare.smt2 \
  nta/sin-sign.smt2 \
  nta/sin-sym2.smt2 \
  nta/sin-sym.smt2 \
  nta/tan-rewrite2.smt2 \
  nta/tan-rewrite.smt2 \
  nta/arrowsmith-050317.smt2 \
  nta/sin-init-tangents.smt2 \
  nta/cos1-tc.smt2 \
  nta/sin1-ub.smt2 \
  nta/sin1-lb.smt2 \
  nta/sin2-ub.smt2 \
  nta/sin2-lb.smt2 \
  nta/exp1-ub.smt2 \
  nta/exp1-lb.smt2 \
  nta/exp-4.5-lt.smt2 \
  nta/exp-n0.5-ub.smt2 \
  nta/exp-n0.5-lb.smt2 \
  nta/dumortier_llibre_artes_ex_5_13.transcendental.k2.smt2 \
  nta/NAVIGATION2.smt2 \
  nta/sin1-sat.smt2 \
  nta/sugar-ident.smt2 \
  nta/sugar-ident-2.smt2 \
  nta/sugar-ident-3.smt2

# unsolved : garbage_collect.cvc

EXTRA_DIST = $(TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
