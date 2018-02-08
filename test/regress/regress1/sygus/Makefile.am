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
	mpg_guard1-dd.sy \
	VC22_a.sy \
	unbdd_inv_gen_ex7.sy \
	three.sy \
	real-grammar.sy \
        lustre-real.sy \
	Base16_1.sy \
	cegar1.sy \
	cggmp.sy \
	clock-inc-tuple.sy \
	dup-op.sy \
	fg_polynomial3.sy \
	hd-01-d1-prog.sy \
	hd-01-d1-prog-dd.sy \
	icfp_14.12.sy \
	icfp_14.12-flip-args.sy \
	icfp_28_10.sy \
	icfp_easy-ite.sy \
	inv-example.sy \
	inv-unused.sy \
	max2-univ.sy \
	multi-fun-polynomial2.sy \
	no-flat-simp.sy \
	process-10-vars.sy \
	tl-type.sy \
	tl-type-4x.sy \
	twolets2-orig.sy \
	unbdd_inv_gen_winf1.sy \


EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
