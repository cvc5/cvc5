TESTS_ENVIRONMENT = @top_builddir@/../../bin/cvc4
TESTS = \
	simple.cvc \
	simple.smt \
	hole6.cvc \
	hole7.cvc \
	hole8.cvc \
	hole9.cvc \
	hole10.cvc \
	wiki.cvc \
	test9.cvc \
	test11.cvc \
	bmc-ibm-1.smt \
	bmc-ibm-2.smt \
	bmc-ibm-3.smt \
	bmc-ibm-4.smt \
	bmc-ibm-5.smt \
	uf20-03.cvc \
	qwh.35.405.shuffled-as.sat03-1651.smt \
	C880mul.miter.shuffled-as.sat03-348.smt \
	instance_1151.smt \
	instance_1444.smt

#Tests that currently do not work
FUTURETESTS = \
	logops.cvc \
	test12.cvc \
	bug1.cvc \
	boolean.cvc

#Tests that take too long to be put in the default regress level
#TODO Make multiple regression levels. Some of which are off by default.
LONGTESTS = \
	friedman_n4_i5.smt \
	friedman_n6_i4.smt \
	bmc-galileo-8.smt \
	bmc-galileo-9.smt \
	bmc-ibm-6.smt \
	bmc-ibm-7.smt \
	bmc-ibm-10.smt \
	bmc-ibm-11.smt \
	bmc-ibm-12.smt \
	bmc-ibm-13.smt \
	comb2.shuffled-as.sat03-420.smt

# synonyms for "check"
.PHONY: regress regress0 regress1 regress2 regress3 test
regress regress0 regress1 regress2 regress3 test: check
