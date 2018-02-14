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

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	sets-disequal.smt2 \
	card-vc6-minimized.smt2 \
	card-4.smt2 \
	fuzz15201.smt2 \
	insert_invariant_37_2.smt2 \
	remove_check_free_31_6.smt2 \
	TalkingAboutSets.hs.fqout.cvc4.3577.smt2 \
	arjun-set-univ.cvc \
	card-3.smt2 \
	card-5.smt2 \
	card-6.smt2 \
	card-7.smt2 \
	copy_check_heap_access_33_4.smt2 \
	deepmeas0.hs.fqout.cvc4.41.smt2 \
	fuzz14418.smt2 \
	fuzz31811.smt2 \
	lemmabug-ListElts317minimized.smt2 \
	ListElem.hs.fqout.cvc4.38.smt2 \
	ListElts.hs.fqout.cvc4.317.smt2 \
	sets-tuple-poly.cvc \
	sharingbug.smt2 \
	UniqueZipper.hs.1030minimized.cvc4.smt2 \
	UniqueZipper.hs.1030minimized2.cvc4.smt2 \
	UniqueZipper.hs.fqout.cvc4.10.smt2 \
	UniqueZipper.hs.fqout.cvc4.1832.smt2 \
	univ-set-uf-elim.smt2
	
EXTRA_DIST = $(TESTS) \
	setofsets-disequal.smt2 

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
