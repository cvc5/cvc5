# -*-makefile-*-
#
# This makefile is the _source_ directory's makefile, and is static,
# not generated.  Makefile.am is the automake makefile for the build
# top-level (its corresponding Makefile.in is here, too, but the
# corresponding Makefile is under builds/$arch/$buildid.
#
builddir = builds

.PHONY: all install examples install-examples
all install examples install-examples .DEFAULT:
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

.PHONY: doc doc-internals
doc: doc-builds
doc-internals: doc-internals-builds

YEAR := $(shell date +%Y)
submission submission-main:
	@if [ -n "`ls src/parser/*/generated 2>/dev/null`" ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please make maintainer-clean first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
        fi
	./autogen.sh
	./configure competition --disable-shared --enable-static-binary --with-cln --with-glpk
	$(MAKE)
	strip builds/bin/cvc4
	$(MAKE) check
	$(MAKE) -C test/regress/regress1 check
	# main track
	mkdir -p cvc4-smteval-$(YEAR)
	cp -p builds/bin/cvc4 cvc4-smteval-$(YEAR)/cvc4
	cp contrib/run-script-smteval2013 cvc4-smteval-$(YEAR)/run
	chmod 755 cvc4-smteval-$(YEAR)/run
	tar cf cvc4-smteval-$(YEAR).tar cvc4-smteval-$(YEAR)
submission-application:
	# application track is a separate build because it has different preprocessor #defines
	@if [ -n "`ls src/parser/*/generated 2>/dev/null`" ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please make maintainer-clean first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
        fi
	./autogen.sh
	./configure competition --disable-shared --enable-static-binary --with-cln --with-glpk CXXFLAGS=-DCVC4_SMTCOMP_APPLICATION_TRACK CFLAGS=-DCVC4_SMTCOMP_APPLICATION_TRACK
	$(MAKE)
	strip builds/bin/cvc4
	$(MAKE) check
	$(MAKE) -C test/regress/regress1 check
	# package the application track tarball
	mkdir -p cvc4-application-smteval-$(YEAR)
	cp -p builds/bin/cvc4 cvc4-application-smteval-$(YEAR)/cvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./cvc4 -L smt2 --no-checking --no-interactive --incremental' ) > cvc4-application-smteval-$(YEAR)/run
	chmod 755 cvc4-application-smteval-$(YEAR)/run
	tar cf cvc4-application-smteval-$(YEAR).tar cvc4-application-smteval-$(YEAR)
submission-parallel:
	# parallel track can't be built with -cln, so it's a separate build
	@if [ -n "`ls src/parser/*/generated 2>/dev/null`" ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please make maintainer-clean first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
        fi
	./autogen.sh
	./configure competition --disable-shared --enable-static-binary --with-gmp --with-portfolio --with-glpk
	$(MAKE)
	strip builds/bin/pcvc4
	# some test cases fail (and are known to fail)
	-$(MAKE) check BINARY=pcvc4
	$(MAKE) -C test/regress/regress1 check BINARY=pcvc4
	# package the parallel track tarball
	mkdir -p cvc4-parallel-smteval-$(YEAR)
	cp -p builds/bin/pcvc4 cvc4-parallel-smteval-$(YEAR)/pcvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./pcvc4 --threads 2 -L smt2 --no-checking --no-interactive' ) > cvc4-parallel-smteval-$(YEAR)/run
	chmod 755 cvc4-parallel-smteval-$(YEAR)/run
	tar cf cvc4-parallel-smteval-$(YEAR).tar cvc4-parallel-smteval-$(YEAR)
