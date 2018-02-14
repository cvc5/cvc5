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
	euf_simp01.smt \
	euf_simp02.smt \
	euf_simp03.smt \
	euf_simp04.smt \
	euf_simp05.smt \
	euf_simp06.smt \
	euf_simp08.smt \
	euf_simp09.smt \
	euf_simp10.smt \
	euf_simp11.smt \
	euf_simp12.smt \
	euf_simp13.smt \
	eq_diamond1.smt \
	eq_diamond14.reduced.smt \
	eq_diamond14.reduced2.smt \
	eq_diamond23.smt \
	NEQ016_size5_reduced2a.smt \
	NEQ016_size5_reduced2b.smt \
	ccredesign-fuzz.smt \
	dead_dnd002.smt \
	iso_brn001.smt \
	simple.01.cvc \
	simple.02.cvc \
	simple.03.cvc \
	simple.04.cvc \
	cnf-iff.smt2 \
	cnf-iff-base.smt2 \
	cnf-ite.smt2 \
	cnf-and-neg.smt2 \
	cnf_abc.smt2 \
	bool-pred-nested.smt2

EXTRA_DIST = $(TESTS) \
	mkpidgeon

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
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
