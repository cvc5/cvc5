TESTS_ENVIRONMENT = @srcdir@/../../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	arrays0.smt2 \
	arrays1.smt2 \
	arrays2.smt2 \
	arrays3.smt2 \
	arrays4.smt2 \
	incorrect1.smt \
	incorrect2.smt \
	incorrect2.minimized.smt \
	incorrect3.smt \
	incorrect4.smt \
	incorrect5.smt \
	incorrect6.smt \
	incorrect7.smt \
	incorrect8.smt \
	incorrect8.minimized.smt \
	incorrect9.smt \
	incorrect10.smt \
	incorrect11.smt

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
