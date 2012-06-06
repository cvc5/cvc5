BINARY = cvc4
if PROOF_REGRESSIONS
TESTS_ENVIRONMENT = LFSC="$(LFSC) $(LFSCARGS)" @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) --proof @top_builddir@/src/main/$(BINARY)
else
TESTS_ENVIRONMENT = @srcdir@/../../run_regression $(RUN_REGRESSION_ARGS) @top_builddir@/src/main/$(BINARY)
endif

override CVC4_REGRESSION_ARGS += --unconstrained-simp
export CVC4_REGRESSION_ARGS

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	arith2.smt2 \
	arith3.smt2 \
	arith4.smt2 \
	arith5.smt2 \
	arith6.smt2 \
	arith7.smt2 \
	arith.smt2 \
	array1.smt2 \
	bvbool3.smt2 \
	bvbool2.smt2 \
	bvbool.smt2 \
	bvcmp.smt2 \
	bvconcat2.smt2 \
	bvconcat.smt2 \
	bvdiv2.smt2 \
	bvdiv.smt2 \
	bvext.smt2 \
	bvite.smt2 \
	bvmul2.smt2 \
	bvmul3.smt2 \
	bvmul.smt2 \
	bvnot.smt2 \
	bvsle2.smt2 \
	bvsle3.smt2 \
	bvsle4.smt2 \
	bvsle5.smt2 \
	bvsle.smt2 \
	bvslt2.smt2 \
	bvslt3.smt2 \
	bvslt4.smt2 \
	bvslt5.smt2 \
	bvslt.smt2 \
	bvule2.smt2 \
	bvule3.smt2 \
	bvule4.smt2 \
	bvule5.smt2 \
	bvule.smt2 \
	bvult2.smt2 \
	bvult3.smt2 \
	bvult4.smt2 \
	bvult5.smt2 \
	bvult.smt2 \
	geq.smt2 \
	gt.smt2 \
	leq.smt2 \
	lt.smt2 \
	uf1.smt2 \
	uf2.smt2 \
	xor.smt2

# bvbool3 takes too long for regress0
EXTRA_DIST = $(TESTS)

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
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
