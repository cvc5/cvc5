SUBDIRS = . precedence uf

TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/src/main/cvc4

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="
TESTS =	\
	boolean-prec.cvc \
	distinct.smt \
	flet.smt \
	flet2.smt \
	ite_real_int_type.smt \
	ite_real_valid.smt \
	let.smt \
	let2.smt \
	simple.smt \
	simple2.smt \
        simple-lra.smt \
        simple-rdl.smt \
	simple-uf.smt \
	ite.smt2 \
	ite2.smt2 \
	ite3.smt2 \
	ite4.smt2 \
        simple-lra.smt2 \
        simple-rdl.smt2 \
	simple-uf.smt2 \
	bug32.cvc \
	bug167.smt \
	bug169.smt \
	hole6.cvc \
	logops.01.cvc \
	logops.02.cvc \
	logops.03.cvc \
	logops.04.cvc \
	logops.05.cvc \
	simple.cvc \
	ineq_basic.smt \
	ineq_slack.smt \
	smallcnf.cvc \
	test11.cvc \
	test9.cvc \
	uf20-03.cvc \
	wiki.01.cvc \
	wiki.02.cvc \
	wiki.03.cvc \
	wiki.04.cvc \
	wiki.05.cvc \
	wiki.06.cvc \
	wiki.07.cvc \
	wiki.08.cvc \
	wiki.09.cvc \
	wiki.10.cvc \
	wiki.11.cvc \
	wiki.12.cvc \
	wiki.13.cvc \
	wiki.14.cvc \
	wiki.15.cvc \
	wiki.16.cvc \
	wiki.17.cvc \
	wiki.18.cvc \
	wiki.19.cvc \
	wiki.20.cvc \
	wiki.21.cvc \
	fuzz_3.smt

if CVC4_BUILD_PROFILE_COMPETITION
else
TESTS += \
	error.cvc
endif

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
