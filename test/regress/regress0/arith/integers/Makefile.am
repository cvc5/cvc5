SUBDIRS = .

# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../../../run_regression
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
	arith-int-004.cvc \
	arith-int-011.cvc \
	arith-int-012.cvc \
	arith-int-013.cvc \
	arith-int-022.cvc \
	arith-int-024.cvc \
	arith-int-042.cvc \
	arith-int-042.min.cvc \
	arith-int-047.cvc \
	arith-int-048.cvc \
	arith-int-050.cvc \
	arith-int-084.cvc \
	arith-int-085.cvc \
	arith-int-097.cvc

EXTRA_DIST = $(TESTS) \
	arith-int-001.cvc \
	arith-int-002.cvc \
	arith-int-003.cvc \
	arith-int-005.cvc \
	arith-int-006.cvc \
	arith-int-008.cvc \
	arith-int-009.cvc \
	arith-int-010.cvc \
	arith-int-014.cvc \
	arith-int-015.cvc \
	arith-int-016.cvc \
	arith-int-017.cvc \
	arith-int-018.cvc \
	arith-int-019.cvc \
	arith-int-020.cvc \
	arith-int-021.cvc \
	arith-int-023.cvc \
	arith-int-025.cvc \
	arith-int-026.cvc \
	arith-int-027.cvc \
	arith-int-028.cvc \
	arith-int-029.cvc \
	arith-int-030.cvc \
	arith-int-031.cvc \
	arith-int-032.cvc \
	arith-int-033.cvc \
	arith-int-034.cvc \
	arith-int-035.cvc \
	arith-int-036.cvc \
	arith-int-037.cvc \
	arith-int-038.cvc \
	arith-int-039.cvc \
	arith-int-040.cvc \
	arith-int-041.cvc \
	arith-int-043.cvc \
	arith-int-044.cvc \
	arith-int-045.cvc \
	arith-int-046.cvc \
	arith-int-049.cvc \
	arith-int-051.cvc \
	arith-int-052.cvc \
	arith-int-053.cvc \
	arith-int-054.cvc \
	arith-int-055.cvc \
	arith-int-056.cvc \
	arith-int-057.cvc \
	arith-int-058.cvc \
	arith-int-059.cvc \
	arith-int-060.cvc \
	arith-int-061.cvc \
	arith-int-062.cvc \
	arith-int-063.cvc \
	arith-int-064.cvc \
	arith-int-065.cvc \
	arith-int-066.cvc \
	arith-int-067.cvc \
	arith-int-068.cvc \
	arith-int-069.cvc \
	arith-int-070.cvc \
	arith-int-071.cvc \
	arith-int-072.cvc \
	arith-int-073.cvc \
	arith-int-074.cvc \
	arith-int-075.cvc \
	arith-int-076.cvc \
	arith-int-077.cvc \
	arith-int-078.cvc \
	arith-int-079.cvc \
	arith-int-080.cvc \
	arith-int-081.cvc \
	arith-int-083.cvc \
	arith-int-086.cvc \
	arith-int-087.cvc \
	arith-int-088.cvc \
	arith-int-089.cvc \
	arith-int-090.cvc \
	arith-int-091.cvc \
	arith-int-092.cvc \
	arith-int-093.cvc \
	arith-int-094.cvc \
	arith-int-095.cvc \
	arith-int-096.cvc \
	arith-int-098.cvc \
	arith-int-099.cvc \
	arith-int-100.cvc

FAILING_TESTS = \
	arith-int-007.cvc \
	arith-int-082.cvc \
	arith-int-098.cvc

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
