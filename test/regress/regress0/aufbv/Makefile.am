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
	bug00.smt \
	bug338.smt2 \
	bug347.smt \
	bug348.smt \
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
	fuzz10.smt \
	fifo32bc06k08.delta01.smt \
	rewrite_bug.smt


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
