SUBDIRS = regress0
DIST_SUBDIRS = regress1 regress2 regress3

export VERBOSE = 1

.PHONY: regress0 regress1 regress2 regress3
regress1: regress0
regress2: regress0 regress1
regress3: regress0 regress1 regress2
regress0 regress1 regress2 regress3:
	-cd $@ && $(MAKE) check

# synonyms for "check"
.PHONY: regress test
regress test: check
