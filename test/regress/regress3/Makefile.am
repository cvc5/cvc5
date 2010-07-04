SUBDIRS = .

TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	C880mul.miter.shuffled-as.sat03-348.smt \
	comb2.shuffled-as.sat03-420.smt \
	hole10.cvc \
	instance_1151.smt

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
.PHONY: regress regress3 test
regress regress3 test: check

# do nothing in this subdir
.PHONY: regress0 regress1 regress2
regress0 regress1 regress2:
