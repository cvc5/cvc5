SUBDIRS = . arith bv aufbv auflia datatypes rewriterules lemmas decision fmf ho nl push-pop quantifiers rels strings sets sygus sep uflia

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
TESTS =	\
	bug425.cvc \
	bug519.smt2 \
	bug521.smt2 \
	bug694-Unapply1.scala-0.smt2 \
	fmf-fun-dbu.smt2 \
	bug296.smt2 \
	bug507.smt2 \
	gensys_brn001.smt2 \
	simplification_bug4.smt2 \
	trim.cvc \
	constarr3.cvc \
	constarr3.smt2 \
	parsing_ringer.cvc \
	arrayinuf_error.smt2 \
	boolean-terms-kernel2.smt2 \
	boolean.cvc \
	bug216.smt2 \
	bug512.smt2 \
	bug516.smt2 \
	bug520.smt2 \
	bug543.smt2 \
	bug567.smt2 \
	bug593.smt2 \
	bug681.smt2 \
	bug800.smt2 \
	bvdiv2.smt2 \
	error.cvc \
	errorcrash.smt2 \
	hole6.cvc \
	ite5.smt2 \
	non-fatal-errors.smt2 \
	proof00.smt2 \
	sqrt2-sort-inf-unk.smt2 \
	test12.cvc \
	uf2.smt2
	
EXTRA_DIST = $(TESTS) \
	simplification_bug4.smt2.expect \
	bug590.smt2.expect \
	bug216.smt2.expect \
	bug590.smt2 \
	bug585.cvc \
	crash_burn_locusts.smt2 \
	bug472.smt2 \
	simple-rdl-definefun.smt2
	
# issue1048-arrays-int-real.smt2 -- different errors on debug and production

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
