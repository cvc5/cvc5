TESTS_ENVIRONMENT = @srcdir@/../../../run_regression @top_builddir@/src/main/cvc4

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
	bv_eq_diamond10.smt
	
EXTRA_DIST = $(TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
