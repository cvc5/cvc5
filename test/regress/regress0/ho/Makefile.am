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
TESTS = \
  cong.smt2 \
  ext-ho-nested-lambda-model.smt2 \
  declare-fun-variants.smt2 \
  ext-ho.smt2 \
  trans.smt2 \
  ext-finite-unsat.smt2 \
  ext-sat.smt2 \
  cong-full-apply.smt2 \
  def-fun-flatten.smt2 \
  lambda-equality-non-canon.smt2 \
  ite-apply-eq.smt2 \
  apply-collapse-unsat.smt2 \
  apply-collapse-sat.smt2 \
  ext-sat-partial-eval.smt2 \
  modulo-func-equality.smt2 \
  ho-matching-enum.smt2 \
  ho-matching-nested-app.smt2 \
  simple-matching.smt2 \
  simple-matching-partial.smt2
  
EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
