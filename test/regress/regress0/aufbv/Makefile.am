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
	bug00.smt \
	bug338.smt2 \
	bug347.smt \
	bug451.smt \
	bug509.smt \
	bug580.smt2 \
	bug580.delta.smt2 \
	try5_small_difret_functions_wp_su.set_char_quoting.il.wp.delta01.smt \
	try3_sameret_functions_fse-bfs_tac.calc_next.il.fse-bfs.delta01.smt \
	diseqprop.01.smt \
	wchains010ue.delta01.smt \
	wchains010ue.delta02.smt \
	dubreva005ue.delta01.smt \
	fuzz00.smt \
	fuzz01.smt \
	fuzz01.delta01.smt \
	fuzz02.delta01.smt \
	fuzz02.smt \
	fuzz03.delta01.smt \
	fuzz03.smt \
	fuzz04.delta01.smt \
	fuzz04.smt \
	fuzz05.delta01.smt \
	fuzz05.smt \
	fuzz06.delta01.smt \
	fuzz06.smt \
	fuzz07.smt \
	fuzz08.smt \
	fuzz09.smt \
	fuzz11.smt \
	fuzz12.smt \
	fuzz13.smt \
	fuzz14.smt \
	fuzz15.smt \
	fifo32bc06k08.delta01.smt \
	rewrite_bug.smt \
	array_rewrite_bug.smt


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
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
