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
	tuple.cvc \
	tuple-model.cvc \
	tuple-record-bug.cvc \
	rec1.cvc \
	rec2.cvc \
	rec4.cvc \
	rec5.cvc \
	datatype.cvc \
	datatype0.cvc \
	datatype1.cvc \
	datatype2.cvc \
	datatype4.cvc \
	datatype13.cvc \
	empty_tuprec.cvc \
	mutually-recursive.cvc \
	pair-real-bool.smt2 \
	pair-bool-bool.cvc \
	rewriter.cvc \
	typed_v10l30054.cvc \
	typed_v1l80005.cvc \
	typed_v2l30079.cvc \
	typed_v3l20092.cvc \
	typed_v5l30069.cvc \
	boolean-equality.cvc \
	boolean-terms-datatype.cvc \
	boolean-terms-parametric-datatype-1.cvc \
	boolean-terms-parametric-datatype-2.cvc \
	boolean-terms-tuple.cvc \
	boolean-terms-record.cvc \
	boolean-terms-rewrite.cvc \
	some-boolean-tests.cvc \
	v10l40099.cvc \
	v2l40025.cvc \
	v3l60006.cvc \
	v5l30058.cvc \
	bug286.cvc \
	bug438.cvc \
	bug438b.cvc \
	wrong-sel-simp.cvc \
	tenum-bug.smt2 \
	cdt-non-canon-stream.smt2 \
	stream-singleton.smt2 \
	is_test.smt2 \
	bug625.smt2 \
	cdt-model-cade15.smt2 \
	sc-cdt1.smt2  \
	conqueue-dt-enum-iloop.smt2 \
	coda_simp_model.smt2 \
	Test1-tup-mp.cvc \
	dt-param-card4-unsat.smt2 \
	dt-param-card4-bool-sat.smt2 \
	bug604.smt2 \
	bug597-rbt.smt2 \
	example-dailler-min.smt2 \
	dt-2.6.smt2  \
	dt-sel-2.6.smt2 \
	dt-param-2.6.smt2 \
	dt-color-2.6.smt2 \
	dt-match-pat-param-2.6.smt2

FAILING_TESTS = \
	datatype-dump.cvc

# takes a long time to build model on debug : datatype3.cvc

EXTRA_DIST = $(TESTS)

if CVC4_BUILD_PROFILE_COMPETITION
else
TESTS += \
	error.cvc
endif

# and make sure to distribute it
EXTRA_DIST += \
	error.cvc \
	$(FAILING_TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
