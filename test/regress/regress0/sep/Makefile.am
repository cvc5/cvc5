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
  pto-01.smt2 \
  pto-02.smt2 \
  pto-04.smt2 \
  sep-01.smt2 \
  sep-02.smt2 \
  sep-03.smt2 \
  sep-find2.smt2 \
  sep-neg-nstrict.smt2 \
  sep-plus1.smt2 \
  sep-nterm-val-model.smt2 \
  crash1220.smt2 \
  nspatial-simp.smt2 \
  sep-neg-1refine.smt2 \
  sep-neg-simple.smt2 \
  sep-simp-unsat-emp.smt2 \
  simple-neg-sat.smt2 \
  wand-simp-sat.smt2 \
  wand-simp-sat2.smt2 \
  wand-simp-unsat.smt2 \
  sep-nterm-again.smt2 \
  nemp.smt2 \
  wand-crash.smt2 \
  wand-nterm-simp.smt2 \
  wand-nterm-simp2.smt2 \
  chain-int.smt2 \
  sep-neg-swap.smt2 \
  sep-neg-nstrict2.smt2 \
  dispose-list-4-init.smt2 \
  wand-0526-sat.smt2 \
  quant_wand.smt2 \
  fmf-nemp-2.smt2 \
  trees-1.smt2 \
  wand-false.smt2 \
  dup-nemp.smt2 \
  emp2-quant-unsat.smt2 \
  dispose-1.smt2 \
  finite-witness-sat.smt2 \
  sep-fmf-priority.smt2


FAILING_TESTS =
# loop-1220.smt2 (slow)

EXTRA_DIST = $(TESTS)

#   slow after changes on Nov 20 : artemis-0512-nonterm.smt2
#   slow after decision engine respects requirePhase: type003.smt2  loop007.smt2 

# and make sure to distribute it
EXTRA_DIST +=

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
