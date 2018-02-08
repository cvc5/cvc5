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
	agree466.smt2 \
	ALG008-1.smt2 \
	bug0909.smt2 \
	bug764.smt2 \
	datatypes-ufinite.smt2 \
	datatypes-ufinite-nested.smt2 \
	fc-pigeonhole19.smt2 \
	fib-core.smt2 \
	fmf-bound-2dim.smt2 \
	fmf-fun-no-elim-ext-arith2.smt2 \
	fmf-strange-bounds.smt2 \
	issue916-fmf-or.smt2 \
	jasmin-cdt-crash.smt2 \
	LeftistHeap.scala-8-ncm.smt2 \
	lst-no-self-rev-exp.smt2 \
	nun-0208-to.smt2 \
	pow2-bool.smt2 \
	with-ind-104-core.smt2	


EXTRA_DIST = $(TESTS)

# synonyms for "check" in this directory
.PHONY: regress regress1 test
regress regress1 test: check

# do nothing in this subdir
.PHONY: regress0 regress2 regress3 regress4
regress0 regress2 regress3 regress4:
