SUBDIRS = . arith precedence uf uflra bv arrays datatypes lemmas push-pop preprocess

if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../run_regression --proof @top_builddir@/src/main/cvc4
else
TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS = \
	distinct.smt \
	flet.smt \
	flet2.smt \
	fuzz_1.smt \
	fuzz_3.smt \
	ineq_basic.smt \
	ineq_slack.smt \
	ite_real_int_type.smt \
	ite_real_valid.smt \
	let.smt \
	let2.smt \
	simplification_bug.smt \
	simplification_bug2.smt \
	simple.smt \
	simple2.smt \
	simple-lra.smt \
	simple-rdl.smt \
	simple-uf.smt

# Regression tests for SMT2 inputs
SMT2_TESTS = \
	ite2.smt2 \
	ite3.smt2 \
	ite4.smt2 \
	simple-lra.smt2 \
	simple-rdl.smt2 \
	simple-uf.smt2

# Regression tests for PL inputs
CVC_TESTS = \
	boolean.cvc \
	boolean-prec.cvc \
	hole6.cvc \
	ite.cvc \
	let.cvc \
	logops.01.cvc \
	logops.02.cvc \
	logops.03.cvc \
	logops.04.cvc \
	logops.05.cvc \
	simple.cvc \
	smallcnf.cvc \
	test9.cvc \
	test11.cvc \
	uf20-03.cvc \
	wiki.01.cvc \
	wiki.02.cvc \
	wiki.03.cvc \
	wiki.04.cvc \
	wiki.05.cvc \
	wiki.06.cvc \
	wiki.07.cvc \
	wiki.08.cvc \
	wiki.09.cvc \
	wiki.10.cvc \
	wiki.11.cvc \
	wiki.12.cvc \
	wiki.13.cvc \
	wiki.14.cvc \
	wiki.15.cvc \
	wiki.16.cvc \
	wiki.17.cvc \
	wiki.18.cvc \
	wiki.19.cvc \
	wiki.20.cvc \
	wiki.21.cvc \
	simplification_bug3.cvc

# Regression tests derived from bug reports
BUG_TESTS = \
	bug32.cvc \
	bug49.smt \
	bug161.smt \
	bug164.smt \
	bug167.smt \
	bug168.smt \
	bug187.smt2 \
	bug220.smt2 \
	bug239.smt \
	buggy-ite.smt2

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	bug216.smt2 \
	bug216.smt2.expect \
	bug288b.smt \
	bug288c.smt \
	bug288.smt

if CVC4_BUILD_PROFILE_COMPETITION
else
TESTS += \
	error.cvc
endif

# and make sure to distribute it
EXTRA_DIST += \
	subranges.cvc \
	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
