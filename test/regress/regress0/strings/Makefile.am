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
  at001.smt2 \
  cardinality.smt2 \
  str001.smt2 \
  str002.smt2 \
  str003.smt2 \
  str004.smt2 \
  str005.smt2 \
  str006.smt2 \
  str007.smt2 \
  fmf001.smt2 \
  fmf002.smt2 \
  model001.smt2 \
  substr001.smt2 \
  regexp001.smt2 \
  regexp002.smt2 \
  loop001.smt2 \
  loop002.smt2 \
  loop003.smt2 \
  loop004.smt2 \
  loop005.smt2 \
  loop006.smt2 \
  loop007.smt2 \
  loop008.smt2 \
  loop009.smt2

FAILING_TESTS =

EXTRA_DIST = $(TESTS)


# and make sure to distribute it
EXTRA_DIST +=

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
