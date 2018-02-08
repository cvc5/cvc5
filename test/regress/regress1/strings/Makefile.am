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
TESTS = \
	cmu-5042-0707-2.smt2 \
	artemis-0512-nonterm.smt2 \
	bug615.smt2 \
	bug682.smt2 \
	bug686dd.smt2 \
	bug768.smt2 \
	bug799-min.smt2 \
	chapman150408.smt2 \
	cmu-disagree-0707-dd.smt2 \
	cmu-inc-nlpp-071516.smt2 \
	cmu-substr-rw.smt2 \
	crash-1019.smt2 \
	csp-prefix-exp-bug.smt2 \
	fmf001.smt2 \
	fmf002.smt2 \
	idof-nconst-index.smt2 \
	kaluza-fl.smt2 \
	loop007.smt2 \
	loop008.smt2 \
	loop009.smt2 \
	nf-ff-contains-abs.smt2 \
	norn-360.smt2 \
	norn-ab.smt2 \
	norn-nel-bug-052116.smt2 \
	pierre150331.smt2 \
	regexp001.smt2 \
	regexp002.smt2 \
	reloop.smt2 \
	str006.smt2 \
	strings-index-empty.smt2 \
	strip-endpt-sound.smt2 \
	substr001.smt2 \
	type002.smt2 \
	type003.smt2 \
	username_checker_min.smt2	


EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
