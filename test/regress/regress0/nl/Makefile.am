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
  coeff-sat.smt2 \
  magnitude-wrong-1020-m.smt2 \
  mult-po.smt2 \
  very-simple-unsat.smt2 \
  subs0-unsat-confirm.smt2 \
  very-easy-sat.smt2 \
  nia-wrong-tl.smt2 \
  real-div-ufnra.smt2 \
  real-as-int.smt2 \
  nta/cos-sig-value.smt2 \
  nta/sin-sym.smt2 \
  nta/tan-rewrite.smt2 \
  nta/exp1-ub.smt2 \
  nta/exp-n0.5-ub.smt2 \
  nta/exp-n0.5-lb.smt2 \
  nta/real-pi.smt2 \
  nta/sqrt-simple.smt2

# unsolved : garbage_collect.cvc

EXTRA_DIST = $(TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
