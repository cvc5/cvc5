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
TESTS = \
	hd-sdiv.sy \
	stopwatch-bt.sy \
	VC22_a.sy \
	unbdd_inv_gen_ex7.sy \
	real-grammar.sy \
	cegar1.sy \
	cggmp.sy \
	clock-inc-tuple.sy \
	dup-op.sy \
	fg_polynomial3.sy \
	hd-01-d1-prog.sy \
	icfp_14.12.sy \
	icfp_14.12-flip-args.sy \
	icfp_28_10.sy \
	icfp_easy-ite.sy \
	inv-example.sy \
	inv-unused.sy \
	multi-fun-polynomial2.sy \
	no-flat-simp.sy \
	process-10-vars.sy \
	tl-type.sy \
	tl-type-4x.sy \
	twolets2-orig.sy \
	unbdd_inv_gen_winf1.sy \
	array_search_2.sy \
	array_sum_2_5.sy \
	commutative.sy \
	constant.sy \
	dt-test-ns.sy \
	hd-19-d1-prog-dup-op.sy \
	list-head-x.sy \
	max.sy \
	nflat-fwd-3.sy \
	nflat-fwd.sy \
	nia-max-square-ns.sy \
	no-mention.sy \
	qe.sy \
	strings-concat-3-args.sy \
	strings-double-rec.sy \
	strings-small.sy \
	strings-template-infer-unused.sy \
	strings-template-infer.sy \
	strings-trivial-simp.sy \
	strings-trivial-two-type.sy \
	strings-trivial.sy \
	sygus-dt.sy \
	tl-type-0.sy \
	triv-type-mismatch-si.sy \
	twolets1.sy

EXTRA_DIST = $(TESTS) \
	enum-test.sy 

# Base16_1.sy

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
