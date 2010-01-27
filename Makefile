builddir = builds

.PHONY: _default_build_ all
_default_build_: all
all %:
	@if test -e $(builddir); then \
		echo cd $(builddir); \
		cd $(builddir); \
		echo $(MAKE) $@; \
		$(MAKE) $@; \
	else \
		echo; \
		echo 'Run configure first, or type "make" in a configured build directory.'; \
		echo; \
	fi

# synonyms for "check"
.PHONY: regress regress0 regress1 regress2 regress3 test
regress regress0 regress1 regress2 regress3 test: check
