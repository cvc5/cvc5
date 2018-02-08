SUBDIRS = . arith bv aufbv auflia datatypes rewriterules lemmas decision fmf ho nl quantifiers rels strings sets sygus sep uflia

# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../run_regression
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
TESTS =	bug425.cvc \
	bug519.smt2 \
	bug521.smt2 \
	bug674.smt2 \
	bug694-Unapply1.scala-0.smt2 \
	fmf-fun-dbu.smt2 \
	bug296.smt2 \
	bug507.smt2 \
	gensys_brn001.smt2 \
	simplification_bug4.smt2 \
	trim.cvc
  
EXTRA_DIST = $(TESTS) \
	simplification_bug4.smt2.expect \
	bug590.smt2.expect \
	bug590.smt2

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
