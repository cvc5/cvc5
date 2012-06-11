BINARY = cvc4
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
	length_trick.smt2 length_trick2.smt2 length_gen_020.smt2 \
	datatypes.smt2 datatypes_sat.smt2 set_A_new_fast_tableau-base.smt2 \
	set_A_new_fast_tableau-base_sat.smt2

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

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
