BINARY=cvc4
if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) --proof @top_builddir@/src/main/$(BINARY)
else
TESTS_ENVIRONMENT = @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	wchains010ue.delta02.smt \
	bitvec0.smt \
	bitvec0.delta01.smt \
	bitvec5.smt \
	quant-Arrays_Q1-noinfer.smt2 \
	uflia-error0.smt2 \
	uflia-xs-09-16-3-4-1-5.smt \
	uflia-xs-09-16-3-4-1-5.delta03.smt \
	bug347.smt

# Incorrect answers:
#	quant-symmetric_unsat_7.smt2 \
#	aufbv-fuzz01.smt \
#

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
