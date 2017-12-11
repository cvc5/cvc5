# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)$(EXEEXT)

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
	jan24/insert_invariant_37_2.smt2 \
	jan24/deepmeas0.hs.fqout.cvc4.47.smt2 \
	jan24/deepmeas0.hs.fqout.small.smt2 \
	jan24/remove_check_free_31_6.smt2 \
	jan27/deepmeas0.hs.fqout.cvc4.41.smt2 \
	jan27/ListConcat.hs.fqout.cvc4.177.smt2 \
	jan27/ListConcat.hs.fqout.177minimized.smt2 \
	jan27/ListElem.hs.fqout.cvc4.38.smt2 \
	jan28/TalkingAboutSets.hs.fqout.3577minimized.smt2 \
	jan30/UniqueZipper.hs.fqout.minimized10.smt2 \
	jan30/UniqueZipper.hs.fqout.cvc4.10.smt2 \
	jan30/UniqueZipper.hs.fqout.minimized1832.smt2 \
	jan30/UniqueZipper.hs.fqout.cvc4.1832.smt2 \
	feb3/ListElts.hs.fqout.cvc4.317.smt2 \
	mar2014/lemmabug-ListElts317minimized.smt2 \
	mar2014/sharing-preregister.smt2 \
	mar2014/small.smt2 \
	mar2014/smaller.smt2 \
	mar2014/UniqueZipper.hs.1030minimized2.cvc4.smt2 \
	mar2014/UniqueZipper.hs.1030minimized.cvc4.smt2 \
	copy_check_heap_access_33_4.smt2 \
	cvc-sample.cvc \
	emptyset.smt2 \
	error1.smt2 \
	error2.smt2 \
	eqtest.smt2 \
	insert.smt2 \
	fuzz14418.smt2 \
	fuzz15201.smt2 \
	fuzz31811.smt2 \
	rec_copy_loop_check_heap_access_43_4.smt2 \
	sets-equal.smt2 \
	sets-inter.smt2 \
	sets-sample.smt2 \
	sets-sharing.smt2 \
	sets-testlemma.smt2 \
	sets-union.smt2 \
	sharingbug.smt2 \
	union-1a-flip.smt2 \
	union-1a.smt2 \
	union-1b-flip.smt2 \
	union-1b.smt2 \
	union-2.smt2 \
	dt-simp-mem.smt2 \
	card3-ground.smt2 \
	card-3sets.cvc \
	card.smt2 \
	card-2.smt2 \
	card-3.smt2 \
	card-4.smt2 \
	card-5.smt2 \
	card-6.smt2 \
	card-7.smt2 \
	abt-min.smt2 \
	abt-te-exh.smt2 \
	abt-te-exh2.smt2 \
	univset-simp.smt2 \
	complement.cvc \
	complement2.cvc \
	complement3.cvc \
	sharing-simp.smt2 \
	pre-proc-univ.smt2 \
	nonvar-univ.smt2 \
	sets-poly-int-real.smt2 \
	sets-poly-nonint.smt2 \
	int-real-univ.smt2 \
	int-real-univ-unsat.smt2 \
	sets-tuple-poly.cvc \
	arjun-set-univ.cvc \
	univ-set-uf-elim.smt2

EXTRA_DIST = $(TESTS)

#if CVC4_BUILD_PROFILE_COMPETITION
#else
#TESTS += \
#	error.cvc
#endif

# disabled tests, yet distribute
EXTRA_DIST += \
	jan28/TalkingAboutSets.hs.fqout.cvc4.3577.smt2 \
	setofsets-disequal.smt2

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
