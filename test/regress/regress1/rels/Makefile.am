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
	bv1p.cvc \
	rel_pressure_0.cvc \
	rel_tc_5_1.cvc \
	set-strat.cvc \
	addr_book_1_1.cvc \
	addr_book_1.cvc \
	bv1-unit.cvc \
	bv1-unitb.cvc \
	bv1.cvc \
	bv1p-sat.cvc \
	bv2.cvc \
	iden_1_1.cvc \
	join-eq-structure_0_1.cvc \
	join-eq-structure-and.cvc \
	join-eq-structure.cvc \
	joinImg_0_1.cvc \
	joinImg_0_2.cvc \
	joinImg_1_1.cvc \
	joinImg_1.cvc \
	joinImg_2_1.cvc \
	joinImg_2.cvc \
	prod-mod-eq.cvc \
	prod-mod-eq2.cvc \
	rel_complex_3.cvc \
	rel_complex_4.cvc \
	rel_complex_5.cvc \
	rel_mix_0_1.cvc \
	rel_tc_10_1.cvc \
	rel_tc_4_1.cvc \
	rel_tc_4.cvc \
	rel_tc_6.cvc \
	rel_tc_9_1.cvc \
	rel_tp_2.cvc \
	rel_tp_join_2_1.cvc \
	strat_0_1.cvc \
	strat.cvc

EXTRA_DIST = $(TESTS) \
	garbage_collect.cvc 

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
