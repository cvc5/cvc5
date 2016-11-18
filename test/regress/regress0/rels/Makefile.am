SUBDIRS = .

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
  addr_book_0.cvc \
  bv2.cvc \
  oneLoc_no_quant-int_0_1.cvc \
  rel_complex_5.cvc \
  rel_join_3_1.cvc \
  rel_product_0_1.cvc \
  rel_tc_10_1.cvc \
  rel_tc_6.cvc \
  rel_tp_join_2_1.cvc \
  rel_transpose_1_1.cvc \
  strat_0_1.cvc \
  addr_book_1_1.cvc \
  prod-mod-eq2.cvc \
  rel_conflict_0.cvc \
  rel_join_3.cvc \
  rel_product_0.cvc \
  rel_tc_11.cvc \
  rel_tc_7.cvc \
  rel_tp_join_2.cvc \
  rel_transpose_1.cvc \
  strat.cvc \
  addr_book_1.cvc \
  join-eq-structure_0_1.cvc \
  prod-mod-eq.cvc \
  rel_join_0_1.cvc \
  rel_join_4.cvc \
  rel_product_1_1.cvc \
  rel_tc_2_1.cvc \
  rel_tp_join_3.cvc \
  rel_transpose_3.cvc \
  bv1.cvc \
  join-eq-structure-and.cvc \
  rel_1tup_0.cvc \
  rel_join_0.cvc \
  rel_join_5.cvc \
  rel_product_1.cvc \
  rel_tc_3_1.cvc \
  rel_tc_9_1.cvc \
  rel_tp_join_eq_0.cvc \
  rel_transpose_4.cvc \
  bv1p.cvc \
  join-eq-structure.cvc \
  rel_complex_0.cvc \
  rel_join_1_1.cvc \
  rel_join_6.cvc \
  rel_symbolic_1_1.cvc \
  rel_tc_3.cvc \
  rel_tp_2.cvc \
  rel_tp_join_int_0.cvc \
  rel_transpose_5.cvc \
  bv1p-sat.cvc \
  join-eq-u.cvc \
  rel_complex_1.cvc \
  rel_join_1.cvc \
  rel_join_7.cvc \
  rel_symbolic_1.cvc \
  rel_tc_4_1.cvc \
  rel_tp_3_1.cvc \
  rel_tp_join_pro_0.cvc \
  rel_transpose_6.cvc \
  bv1-unitb.cvc \
  join-eq-u-sat.cvc \
  rel_complex_3.cvc \
  rel_join_2_1.cvc \
  rel_mix_0_1.cvc \
  rel_symbolic_2_1.cvc \
  rel_tc_4.cvc \
  rel_tp_join_0.cvc \
  rel_tp_join_var_0.cvc \
  rel_transpose_7.cvc \
  bv1-unit.cvc \
  rel_complex_4.cvc \
  rel_join_2.cvc \
  rel_pressure_0.cvc \
  rel_symbolic_3_1.cvc \
  rel_tc_5_1.cvc \
  rel_tp_join_1.cvc \
  rel_transpose_0.cvc \
  set-strat.cvc

# unsolved : garbage_collect.cvc
# dump-unsat-core crash : rel_tc_8.cvc

EXTRA_DIST = $(TESTS)

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
