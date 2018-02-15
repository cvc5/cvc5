# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)$(EXEEXT)

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
        parity-AIG-d0.sy \
        const-var-test.sy \
        no-syntax-test.sy \
        let-ringer.sy \
        let-simp.sy \
        no-syntax-test-bool.sy \
        uminus_one.sy \
        dt-no-syntax.sy \
        strings-unconstrained.sy \
        General_plus10.sy \
        parse-bv-let.sy \
        ccp16.lus.sy \
        real-si-all.sy  \
        c100.sy \
        check-generic-red.sy

# sygus tests currently taking too long for make regress
EXTRA_DIST = $(TESTS) \
  sygus-uf.sl

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
