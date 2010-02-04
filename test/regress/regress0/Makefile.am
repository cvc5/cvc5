TESTS_ENVIRONMENT = @srcdir@/../run_regression @top_builddir@/../../bin/cvc4
TESTS =	boolean.cvc \
	bug1.cvc \
	hole6.cvc \
	logops.cvc \
	queries0.cvc \
	simple2.smt \
	simple.cvc \
	simple.smt \
	simple-uf.smt \
	smallcnf.cvc \
	test11.cvc \
	test12.cvc \
	test9.cvc \
	uf20-03.cvc \
	wiki.cvc

# synonyms for "check"
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
