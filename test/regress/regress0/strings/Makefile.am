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
  bug001.smt2 \
  bug002.smt2 \
  escchar.smt2 \
  escchar_25.smt2 \
  str003.smt2 \
  str004.smt2 \
  str005.smt2 \
  type001.smt2 \
  model001.smt2 \
  leadingzero001.smt2 \
  loop001.smt2 \
  unsound-0908.smt2 \
  ilc-like.smt2 \
  indexof-sym-simp.smt2 \
  bug613.smt2 \
  norn-simp-rew.smt2 \
  bug612.smt2 \
  idof-rewrites.smt2 \
  norn-31.smt2 \
  strings-native-simple.cvc \
  strings-charat.cvc \
  issue1189.smt2 \
  rewrites-v2.smt2 \
  substr-rewrites.smt2 \
  repl-rewrites2.smt2

FAILING_TESTS =

EXTRA_DIST = $(TESTS)

# and make sure to distribute it
EXTRA_DIST +=

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
