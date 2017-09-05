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
TESTS = \
  at001.smt2 \
  bug001.smt2 \
  bug002.smt2 \
  escchar.smt2 \
  escchar_25.smt2 \
  str001.smt2 \
  str002.smt2 \
  str003.smt2 \
  str004.smt2 \
  str005.smt2 \
  str006.smt2 \
  str007.smt2 \
  fmf002.smt2 \
  type001.smt2 \
  type003.smt2 \
  model001.smt2 \
  substr001.smt2 \
  regexp001.smt2 \
  regexp002.smt2 \
  regexp003.smt2 \
  leadingzero001.smt2 \
  loop001.smt2 \
  loop002.smt2 \
  loop003.smt2 \
  loop004.smt2 \
  loop005.smt2 \
  loop006.smt2 \
  loop007.smt2 \
  loop008.smt2 \
  loop009.smt2 \
  reloop.smt2 \
  unsound-0908.smt2 \
  ilc-like.smt2 \ 
  ilc-l-nt.smt2 \ 
  artemis-0512-nonterm.smt2 \
  indexof-sym-simp.smt2 \
  bug613.smt2 \
  idof-triv.smt2 \
  chapman150408.smt2 \
  pierre150331.smt2 \
  norn-360.smt2 \
  norn-simp-rew.smt2 \
  norn-simp-rew-sat.smt2 \
  idof-nconst-index.smt2 \
  idof-neg-index.smt2 \
  bug612.smt2 \
  bug615.smt2 \
  kaluza-fl.smt2 \
  idof-rewrites.smt2 \
  bug682.smt2 \
  bug686dd.smt2 \
  idof-handg.smt2 \
  fmf001.smt2 \
  crash-1019.smt2 \
  norn-31.smt2 \
  strings-native-simple.cvc \
  cmu-2db2-extf-reg.smt2 \
  norn-nel-bug-052116.smt2 \
  cmu-disagree-0707-dd.smt2 \
  nf-ff-contains-abs.smt2  \
  csp-prefix-exp-bug.smt2 \
  cmu-substr-rw.smt2 \
  gm-inc-071516-2.smt2 \
  cmu-inc-nlpp-071516.smt2 \
  strings-index-empty.smt2 \
  bug768.smt2 \
  username_checker_min.smt2 \
  repl-empty-sem.smt2 \
  bug799-min.smt2 \
  strings-charat.cvc

FAILING_TESTS =

EXTRA_DIST = $(TESTS)

# and make sure to distribute it
EXTRA_DIST +=

#norn-dis-0707-3.smt2
#norn-ab.smt2
#type002.smt2

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3 regress4
regress1 regress2 regress3 regress4:
