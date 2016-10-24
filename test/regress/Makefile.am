SUBDIRS = regress0
DIST_SUBDIRS = regress0 regress1 regress2 regress3 regress4

@mk_include@ @srcdir@/Makefile.levels

MAKEFLAGS = -k

export VERBOSE = 1

.PHONY: regress0 regress1 regress2 regress3 regress4
regress1: regress0
regress2: regress0 regress1
regress3: regress0 regress1 regress2
regress4: regress0 regress1 regress2 regress3
regress0 regress1 regress2 regress3 regress4:
	-cd $@ && $(MAKE) check

# synonyms for "check" in this directory
.PHONY: regress test
regress test: check

# no-ops here
.PHONY: units systemtests
units systemtests:

EXTRA_DIST = \
	Makefile.levels \
	run_regression \
	README
