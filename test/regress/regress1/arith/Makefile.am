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
	arith-int-004.cvc \
	arith-int-011.cvc \
	arith-int-012.cvc \
	arith-int-013.cvc \
	arith-int-022.cvc \
	arith-int-024.cvc \
	arith-int-042.cvc \
	arith-int-042.min.cvc \
	arith-int-047.cvc \
	arith-int-048.cvc \
	arith-int-050.cvc \
	arith-int-084.cvc \
	arith-int-085.cvc \
	arith-int-097.cvc \
	bug716.0.smt2 \
	problem__003.smt2


EXTRA_DIST = $(TESTS) \
	arith-int-008.cvc \
	arith-int-018.cvc \
	arith-int-020.cvc \
	arith-int-026.cvc \
	arith-int-029.cvc \
	arith-int-030.cvc \
	arith-int-043.cvc \
	arith-int-044.cvc \
	arith-int-049.cvc \
	arith-int-061.cvc \
	arith-int-062.cvc \
	arith-int-064.cvc \
	arith-int-065.cvc \
	arith-int-081.cvc \
	arith-int-083.cvc \
	arith-int-090.cvc \
	arith-int-091.cvc \
	arith-int-092.cvc \
	arith-int-094.cvc \
	arith-int-096.cvc \
	arith-int-098.cvc

EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
