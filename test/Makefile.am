SUBDIRS = unit system regress

.PHONY: regress0 regress1 regress2 regress3
regress0 regress1 regress2 regress3:
	for dir in $(SUBDIRS); do \
		(cd $$dir && $(MAKE) $(AM_MAKEFLAGS) $@) || exit 1; \
	done

# synonyms for "check"
.PHONY: regress test
regress test: check
