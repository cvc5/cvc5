SUBDIRS = . arith precedence uf uflra uflia bv arrays aufbv auflia datatypes quantifiers lemmas push-pop preprocess unconstrained decision
DIST_SUBDIRS = . arith precedence uf uflra uflia bv arrays aufbv auflia datatypes quantifiers rewriterules lemmas push-pop preprocess unconstrained decision

BINARY = cvc4
if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../run_regression $(RUN_REGRESSION_ARGS) --proof @top_builddir@/src/main/$(BINARY)
else
TESTS_ENVIRONMENT = @srcdir@/../run_regression $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)
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
	simple-uf.smt2 \
	simplification_bug4.smt2 \
	parallel-let.smt2

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

# Regression tests for TPTP inputs
TPTP_TESTS = \
	tptp_parser.p \
	tptp_parser2.p \
	tptp_parser3.p \
	tptp_parser4.p \
	tptp_parser5.p \
	tptp_parser6.p \
	tptp_parser7.p \
	tptp_parser8.p \
	tptp_parser9.p \
	tptp_parser10.p

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
	bug288.smt \
	bug288b.smt \
	bug288c.smt \
	buggy-ite.smt2 \
	bug303.smt2 \
	bug310.cvc \
	bug322.cvc \
	bug322b.cvc \
	bug339.smt2 \
	bug365.smt2

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(TPTP_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	simplification_bug4.smt2.expect

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
