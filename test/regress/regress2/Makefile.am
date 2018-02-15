SUBDIRS = . arith nl quantifiers strings sygus

# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../run_regression
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
	bug136.smt \
	bug148.smt \
	bug394.smt2 \
	DTP_k2_n35_c175_s15.smt2 \
	GEO123+1.minimized.smt2 \
	error1.smt \
	friedman_n4_i5.smt \
	hole7.cvc \
	hole8.cvc \
	instance_1444.smt \
	fuzz_2.smt \
	hash_sat_10_09.smt2 \
	hash_sat_07_17.smt2 \
	ooo.tag10.smt2 \
	hash_sat_06_19.smt2 \
	hash_sat_09_09.smt2 \
	ooo.rf6.smt2 \
	auflia-fuzz06.smt \
	piVC_5581bd.smt2 \
	typed_v1l50016-simp.cvc \
	FIREFLY_3_e2_2236_e7_3681.ec.minimized.smt2 \
	xs-09-16-3-4-1-5.smt \
	xs-09-16-3-4-1-5.decn.smt \
	uflia-error0.smt2 \
	bug812.smt2 \
	bug765.smt2 \
	simplify.javafe.ast.ArrayInit.35_without_quantification2.smt2 \
	bug674.smt2
 
EXTRA_DIST = $(TESTS) \
	FIREFLY_3_e2_2236_e7_3681.ec.minimized.smt2.expect \
	uflia-error0.smt2.expect \
	xs-09-16-3-4-1-5.decn.smt.expect \
	bug396.smt2 \
	javafe.ast.StandardPrettyPrint.319_no_forall.smt2 \
	javafe.ast.WhileStmt.447_no_forall.smt2

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
.PHONY: regress regress2 test
regress regress2 test: check

# do nothing in this subdir
.PHONY: regress0 regress1 regress3 regress4
regress0 regress1 regress3 regress4:
