TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS = \
	and-xor.cvc \
	and-not.cvc \
        bool-cmp.cvc \
        cmp-plus.cvc \
	eq-fun.cvc \
	iff-assoc.cvc \
	iff-implies.cvc \
	implies-assoc.cvc \
	implies-iff.cvc \
	implies-or.cvc \
	not-and.cvc \
	not-eq.cvc \
	or-implies.cvc \
	or-xor.cvc \
        plus-mult.cvc \
	xor-or.cvc \
	xor-and.cvc \
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
