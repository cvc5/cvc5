# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../../run_regression
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
	concat-merge-0.smt \
	concat-merge-1.smt \
	concat-merge-2.smt \
	concat-merge-3.smt \
	extract-concat-0.smt \
	extract-concat-1.smt \
	extract-concat-2.smt \
	extract-concat-3.smt \
	extract-concat-4.smt \
	extract-concat-5.smt \
	extract-concat-6.smt \
	extract-concat-7.smt \
	extract-concat-8.smt \
	extract-concat-9.smt \
	extract-concat-10.smt \
	extract-concat-11.smt \
	extract-constant.smt \
	extract-extract-0.smt \
	extract-extract-1.smt \
	extract-extract-2.smt \
	extract-extract-3.smt \
	extract-extract-4.smt \
	extract-extract-5.smt \
	extract-extract-6.smt \
	extract-extract-7.smt \
	extract-extract-8.smt \
	extract-extract-9.smt \
	extract-extract-10.smt \
	extract-extract-11.smt \
	extract-whole-0.smt \
	extract-whole-1.smt \
	extract-whole-2.smt \
	extract-whole-3.smt \
	extract-whole-4.smt \
	equality-00.smt \
	equality-01.smt \
	equality-02.smt \
	equality-05.smt \
	bv_eq_diamond10.smt \
	slice-01.smt \
	slice-02.smt \
	slice-03.smt \
	slice-04.smt \
	slice-05.smt \
	slice-06.smt \
	slice-07.smt \
	slice-08.smt \
	slice-09.smt \
	slice-10.smt \
	slice-11.smt \
	slice-12.smt \
	slice-13.smt \
	slice-14.smt \
	slice-15.smt \
	slice-16.smt \
	slice-17.smt \
	slice-18.smt \
	slice-19.smt \
	slice-20.smt \
	a78test0002.smt \
	a95test0002.smt \
	bitvec0.smt \
	bitvec2.smt \
	bitvec5.smt \
	bitvec7.smt

EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
