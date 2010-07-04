TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS = \
	iff-implies.cvc \
	implies-iff.cvc \
	implies-or.cvc \
	or-implies.cvc \
	or-xor.cvc \
	xor-or.cvc \
	xor-and.cvc \
	and-xor.cvc \
	and-not.cvc \
	not-and.cvc \
	not-eq.cvc \
	eq-fun.cvc \
	iff-assoc.cvc \
	implies-assoc.cvc \
	xor-assoc.cvc

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
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
