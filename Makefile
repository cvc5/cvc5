# -*-makefile-*-
#
# This makefile is the _source_ directory's makefile, and is static,
# not generated.  Makefile.am is the automake makefile for the build
# top-level (its corresponding Makefile.in is here, too, but the
# corresponding Makefile is under builds/$arch/$buildid.
#
builddir = builds

.PHONY: all
all .DEFAULT:
	@if test -d $(builddir); then \
		echo cd $(builddir); \
		cd $(builddir); \
		echo $(MAKE) $@; \
		$(MAKE) $@ || exit 1; \
	else \
		echo; \
		echo 'Run configure first, or type "make" in a configured build directory.'; \
		echo; \
	fi

distclean maintainerclean:
	@if test -d $(builddir); then \
		echo cd $(builddir); \
		cd $(builddir); \
		echo $(MAKE) $@; \
		$(MAKE) $@ || exit 1; \
	fi
	test -z "$(builddir)" || rm -fr "$(builddir)"
	rm -f config.reconfig

# synonyms for "check"
.PHONY: test
test: check

.PHONY: doc
doc: doc-builds

.PHONY: examples
examples: all
	(cd examples && $(MAKE) $(AM_MAKEFLAGS))

YEAR := $(shell date +%Y)
submission:
	if [ ! -e configure ]; then ./autogen.sh; fi
	./configure competition --disable-shared --enable-static-binary --with-cln --with-portfolio
	$(MAKE)
	strip builds/bin/cvc4
	$(MAKE) regress1
	strip builds/bin/pcvc4
	$(MAKE) regress1 BINARY=pcvc4
	# main track
	mkdir -p cvc4-smtcomp-$(YEAR)
	cp -p builds/bin/cvc4 cvc4-smtcomp-$(YEAR)/cvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./cvc4 -L smt2 --no-interactive' ) > cvc4-smtcomp-$(YEAR)/run
	chmod 755 cvc4-smtcomp-$(YEAR)/run
	tar cf cvc4-smtcomp-$(YEAR).tar cvc4-smtcomp-$(YEAR)
	# parallel track
	mkdir -p cvc4-parallel-smtcomp-$(YEAR)
	cp -p builds/bin/pcvc4 cvc4-parallel-smtcomp-$(YEAR)/pcvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./pcvc4 -L smt2 --no-interactive' ) > cvc4-parallel-smtcomp-$(YEAR)/run
	chmod 755 cvc4-parallel-smtcomp-$(YEAR)/run
	tar cf cvc4-parallel-smtcomp-$(YEAR).tar cvc4-parallel-smtcomp-$(YEAR)
	# application track
	mkdir -p cvc4-application-smtcomp-$(YEAR)
	cp -p builds/bin/cvc4 cvc4-application-smtcomp-$(YEAR)/cvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./cvc4 -L smt2 --no-interactive --incremental' ) > cvc4-application-smtcomp-$(YEAR)/run
	chmod 755 cvc4-application-smtcomp-$(YEAR)/run
	tar cf cvc4-application-smtcomp-$(YEAR).tar cvc4-application-smtcomp-$(YEAR)
