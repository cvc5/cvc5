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
  bug698.smt2

# unsolved : garbage_collect.cvc

EXTRA_DIST = $(TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
