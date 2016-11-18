# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @abs_top_builddir@/src/main/$(BINARY)$(EXEEXT)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

MAKEFLAGS = -k

# escape the `=' in file names
equals = =

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	tptp_parser.p \
	tptp_parser2.p \
	tptp_parser3.p \
	tptp_parser4.p \
	tptp_parser5.p \
	tptp_parser6.p \
	tptp_parser7.p \
	tptp_parser8.p \
	tptp_parser9.p \
	tptp_parser10.p \
	tff0.p \
	tff0-arith.p \
	ARI086$(equals)1.p \
	DAT001$(equals)1.p \
	KRS018+1.p \
	KRS063+1.p \
	MGT019+2.p \
	MGT041-2.p \
	PUZ131_1.p \
	SYN000+1.p \
	SYN000+2.p \
	SYN000-1.p \
	SYN000-2.p \
	SYN000$(equals)2.p \
	SYN000_1.p \
	SYN000_2.p \
	SYN075-1.p

# axiom files required for the above tests
TEST_DEPS_DIST = \
	Axioms/BOO004-0.ax \
	Axioms/SYN000_0.ax \
	Axioms/SYN000-0.ax \
	Axioms/SYN000+0.ax

# these take too long at present
EXTRA_DIST = $(TESTS) \
	$(TEST_DEPS_DIST) \
	BOO027-1.p \
	BOO003-4.p \
	MGT031-1.p \
	NLP114-1.p \
	SYN075+1.p

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
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
