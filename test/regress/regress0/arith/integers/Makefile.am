SUBDIRS = .

TESTS_ENVIRONMENT = @srcdir@/../../../run_regression @top_builddir@/src/main/cvc4
MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	arith-int-001.cvc \
	arith-int-002.cvc \
	arith-int-003.cvc \
	arith-int-004.cvc \
	arith-int-005.cvc \
	arith-int-006.cvc \
	arith-int-007.cvc \
	arith-int-009.cvc \
	arith-int-010.cvc \
	arith-int-011.cvc \
	arith-int-014.cvc \
	arith-int-015.cvc \
	arith-int-016.cvc \
	arith-int-017.cvc \
	arith-int-018.cvc \
	arith-int-019.cvc \
	arith-int-020.cvc 

EXTRA_DIST = $(TESTS) \
	arith-int-008.cvc \
	arith-int-012.cvc \
	arith-int-013.cvc \
	arith-int-022.cvc \
	arith-int-042.cvc \
	arith-int-042.min.cvc \
	arith-int-043.cvc \
	arith-int-047.cvc \
	arith-int-050.cvc \
	arith-int-082.cvc \
	arith-int-084.cvc \
	arith-int-097.cvc \
	arith-int-098.cvc \
	arith-int-100.cvc

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif
#
# and make sure to distribute it
#EXTRA_DIST += \
#	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
