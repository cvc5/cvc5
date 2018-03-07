DIST_SUBDIRS = regress0 regress1 regress2 regress3 regress4

include Makefile.tests

TESTS = $(REG0_TESTS) $(REG1_TESTS) $(REG2_TESTS) $(REG3_TESTS) $(REG4_TESTS)

@mk_include@ @srcdir@/Makefile.levels

# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_DRIVER = env AM_TAP_AWK='$(AWK)' $(SHELL) \
			 	 $(top_srcdir)/config/tap-driver.sh
LOG_COMPILER = python @abs_top_srcdir@/test/regress/run_regression.py
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @abs_top_builddir@/src/main/$(BINARY)$(EXEEXT)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

MAKEFLAGS = -k

export VERBOSE = 1
.PHONY: regress0 regress1 regress2 regress3 regress4

regress0:
	REGRESSION_LEVEL=0 $(MAKE) check

regress1:
	REGRESSION_LEVEL=1 $(MAKE) check

regress2:
	REGRESSION_LEVEL=2 $(MAKE) check

regress3:
	REGRESSION_LEVEL=3 $(MAKE) check

regress4:
	REGRESSION_LEVEL=4 $(MAKE) check

EXTRA_DIST = \
  $(TESTS) \
  $(TESTS_EXPECT) \
	regress0/uf/mkpidgeon \
	Makefile.levels \
	Makefile.tests \
	run_regression \
	README
