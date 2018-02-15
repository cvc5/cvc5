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
	ForElimination-scala-9.smt2 \
	javafe.ast.ArrayInit.35.smt2 \
	javafe.ast.StandardPrettyPrint.319.smt2 \
	javafe.ast.WhileStmt.447.smt2 \
	javafe.tc.CheckCompilationUnit.001.smt2 \
	javafe.tc.FlowInsensitiveChecks.682.smt2 \
	nunchaku2309663.nun.min.smt2 \
	AdditiveMethods_AdditiveMethods..ctor.smt2

EXTRA_DIST = $(TESTS) \
	small-bug1-fixpoint-3.smt2

# synonyms for "check" in this directory
.PHONY: regress regress2 test
regress regress2 test: check

# do nothing in this subdir
.PHONY: regress0 regress1 regress3 regress4
regress0 regress1 regress3 regress4:
