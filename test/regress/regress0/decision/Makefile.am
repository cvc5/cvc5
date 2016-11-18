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

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	wchains010ue.delta02.smt \
	bitvec0.smt \
	bitvec0.delta01.smt \
	bitvec5.smt \
	quant-Arrays_Q1-noinfer.smt2 \
	quant-ex1.smt2 \
	uflia-xs-09-16-3-4-1-5.delta03.smt \
	aufbv-fuzz01.smt \
	bug347.smt \
	bug374a.smt \
	bug374b.smt2 \
	error20.smt \
	error20.delta01.smt \
	error122.smt \
	error122.delta01.smt \
	error3.delta01.smt \
	pp-regfile.delta01.smt \
	pp-regfile.delta02.smt

EXTRA_DIST = $(TESTS) \
	aufbv-fuzz01.smt.expect \
	pp-regfile.delta01.smt.expect \
	bitvec0.delta01.smt.expect \
	pp-regfile.delta02.smt.expect \
	uflia-xs-09-16-3-4-1-5.delta03.smt.expect \
	bitvec0.smt.expect \
	bitvec5.smt.expect \
	quant-Arrays_Q1-noinfer.smt2.expect \
	wchains010ue.delta02.smt.expect \
	bug347.smt.expect \
	bug374a.smt.expect \
	bug374b.smt2.expect \
	quant-ex1.disable_miniscope.smt2.expect \
	wchains010ue.smt.expect \
	just_sat.expect \
	quant-ex1.smt2.expect \
	just_unsat.expect \
	quant-symmetric_unsat_7.smt2.expect

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
