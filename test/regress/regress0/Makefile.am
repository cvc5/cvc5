SUBDIRS = . expect arith precedence uf uflra uflia bv arrays aufbv auflia datatypes quantifiers rewriterules lemmas push-pop preprocess tptp unconstrained decision fmf strings sets rels parser sygus sep nl ho
DIST_SUBDIRS = $(SUBDIRS)

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
	simple-uf.smt \
	constant-rewrite.smt

# Regression tests for SMT2 inputs
SMT2_TESTS = \
	arrayinuf_declare.smt2 \
	boolean-terms-kernel1.smt2 \
	boolean-terms-bug-array.smt2 \
	chained-equality.smt2 \
	ite2.smt2 \
	ite3.smt2 \
	ite4.smt2 \
	simple-lra.smt2 \
	simple-rdl.smt2 \
	simple-uf.smt2 \
	parallel-let.smt2 \
	get-value-incremental.smt2 \
	get-value-reals.smt2 \
	get-value-ints.smt2 \
	get-value-reals-ints.smt2 \
	hung13sdk_output1.smt2 \
	hung10_itesdk_output2.smt2 \
	hung10_itesdk_output1.smt2 \
	hung13sdk_output2.smt2 \
	declare-funs.smt2 \
	declare-fun-is-match.smt2 \
	issue1063-overloading-dt-cons.smt2 \
	issue1063-overloading-dt-sel.smt2 \
	issue1063-overloading-dt-fun.smt2 \
	reset-assertions.smt2 \
	rec-fun-const-parse-bug.smt2

# Regression tests for PL inputs
CVC_TESTS = \
	boolean-prec.cvc \
	boolean-terms.cvc \
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
	queries0.cvc \
	print_lambda.cvc \
	cvc3.userdoc.01.cvc \
	cvc3.userdoc.02.cvc \
	cvc3.userdoc.03.cvc \
	cvc3.userdoc.04.cvc \
	cvc3.userdoc.05.cvc \
	cvc3.userdoc.06.cvc

# Regression tests for TPTP inputs
TPTP_TESTS =

# Regression tests derived from bug reports
BUG_TESTS = \
	smt2output.smt2 \
	bug32.cvc \
	bug49.smt \
	bug161.smt \
	bug164.smt \
	bug167.smt \
	bug168.smt \
	bug187.smt2 \
	bug217.smt2 \
	bug220.smt2 \
	bug239.smt \
	bug274.cvc \
	bug288.smt \
	bug288b.smt \
	bug288c.smt \
	buggy-ite.smt2 \
	bug303.smt2 \
	bug310.cvc \
	bug322.cvc \
	bug322b.cvc \
	bug339.smt2 \
	bug365.smt2 \
	bug382.smt2 \
	bug383.smt2 \
	bug398.smt2 \
	bug421.smt2 \
	bug421b.smt2 \
	bug480.smt2 \
	bug484.smt2 \
	bug486.cvc \
	bug512.minimized.smt2 \
	bug521.minimized.smt2 \
	bug522.smt2 \
	bug528a.smt2 \
	bug541.smt2 \
	bug544.smt2 \
	bug548a.smt2 \
	bug576.smt2 \
	bug576a.smt2 \
	bug578.smt2 \
	bug586.cvc \
	bug595.cvc \
	bug596.cvc \
	bug596b.cvc \
	bug605.cvc \
	bug639.smt2 \
	bt-test-00.smt2 \
	bt-test-01.smt2 \
	bug1247.smt2

TESTS = $(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(TPTP_TESTS) $(BUG_TESTS)

# bug512 -- taking too long, --time-per not working perhaps? in any case,
# we have a minimized version still getting tested
# bug639 -- still fails, reopened bug
# bug585 -- contains subrange type (not supported)


EXTRA_DIST = $(TESTS)

# and make sure to distribute it
EXTRA_DIST += $(DISABLED_TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
