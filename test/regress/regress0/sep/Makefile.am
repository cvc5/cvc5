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
  sep-01.smt2 \
  sep-plus1.smt2 \
  nspatial-simp.smt2 \
  sep-simp-unsat-emp.smt2 \
  nemp.smt2 \
  wand-crash.smt2 \
  trees-1.smt2 \
  dup-nemp.smt2 \
  dispose-1.smt2 \
  nil-no-elim.smt2


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
