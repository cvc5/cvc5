SUBDIRS = .

TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	friedman_n4_i5.smt \
	hole7.cvc \
	hole8.cvc \
	instance_1444.smt \
	fuzz_1.smt \
	fuzz_2.smt

EXTRA_DIST = $(TESTS)

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check"
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3
regress0 regress2 regress3:
