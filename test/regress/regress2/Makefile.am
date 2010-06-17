SUBDIRS = .

TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	bmc-galileo-8.smt \
	bmc-galileo-9.smt \
	bmc-ibm-10.smt \
	bmc-ibm-11.smt \
	bmc-ibm-12.smt \
	bmc-ibm-13.smt \
	bmc-ibm-1.smt \
	bmc-ibm-2.smt \
	bmc-ibm-3.smt \
	bmc-ibm-4.smt \
	bmc-ibm-5.smt \
	bmc-ibm-6.smt \
	bmc-ibm-7.smt \
	friedman_n6_i4.smt \
	hole9.cvc \
	qwh.35.405.shuffled-as.sat03-1651.smt

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif

# synonyms for "check"
.PHONY: regress regress2 test
regress regress2 test: check

# do nothing in this subdir
.PHONY: regress0 regress1 regress3
regress0 regress1 regress3:
