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
.PHONY: regress test
regress test: check

submission:
	if [ ! -e configure ]; then ./autogen.sh; fi
	./configure competition
	$(MAKE)
	mkdir -p cvc4-smtcomp-2010
	cp -p $(top_builddir)/bin/cvc4 cvc4-smtcomp-2010/cvc4
	cp -p contrib/run-smtcomp cvc4-smtcomp-2010/run
	tar cfz cvc4-smtcomp-2010.tgz cvc4-smtcomp-2010
