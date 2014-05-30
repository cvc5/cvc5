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
		$(MAKE) show-config; \
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
	./configure competition --disable-shared --enable-static-binary --with-cln --with-glpk --enable-gpl
	$(MAKE)
	strip builds/bin/cvc4
	$(MAKE) check
	#$(MAKE) -C test/regress/regress1 check
	# main track
	mkdir -p cvc4-smtcomp-$(YEAR)
	cp -p builds/bin/cvc4 cvc4-smtcomp-$(YEAR)/cvc4
	mkdir cvc4-smtcomp-$(YEAR)/bin
	cp contrib/run-script-smtcomp2014 cvc4-smtcomp-$(YEAR)/bin/starexec_run_default
	chmod 755 cvc4-smtcomp-$(YEAR)/bin/starexec_run_default
	#echo "CVC4 for SMT-COMP main track `builds/bin/cvc4 --version`" > cvc4-smtcomp-$(YEAR)/starexec_description.txt
	cd cvc4-smtcomp-$(YEAR) && zip -r ../cvc4-smtcomp-$(YEAR).zip *
submission-application:
	# application track is a separate build because it has different preprocessor #defines
	@if [ -n "`ls src/parser/*/generated 2>/dev/null`" ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please make maintainer-clean first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	./autogen.sh
	./configure competition --disable-shared --enable-static-binary --with-cln --with-glpk --enable-gpl CXXFLAGS=-DCVC4_SMTCOMP_APPLICATION_TRACK CFLAGS=-DCVC4_SMTCOMP_APPLICATION_TRACK
	$(MAKE)
	strip builds/bin/cvc4
	$(MAKE) check
	#$(MAKE) -C test/regress/regress1 check
	# package the application track zipfile
	mkdir -p cvc4-application-smtcomp-$(YEAR)
	cp -p builds/bin/cvc4 cvc4-application-smtcomp-$(YEAR)/cvc4
	mkdir cvc4-application-smtcomp-$(YEAR)/bin
	cp contrib/run-script-smtcomp2014-application cvc4-application-smtcomp-$(YEAR)/bin/starexec_run_default
	chmod 755 cvc4-application-smtcomp-$(YEAR)/bin/starexec_run_default
	#echo "CVC4 for SMT-COMP application track `builds/bin/cvc4 --version`" > cvc4-application-smtcomp-$(YEAR)/starexec_description.txt
	cd cvc4-application-smtcomp-$(YEAR) && zip -r ../cvc4-application-smtcomp-$(YEAR).zip *
submission-parallel:
	# parallel track can't be built with -cln, so it's a separate build
	@if [ -n "`ls src/parser/*/generated 2>/dev/null`" ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please make maintainer-clean first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	./autogen.sh
	./configure competition --disable-shared --enable-static-binary --with-gmp --with-portfolio --with-glpk --enable-gpl
	$(MAKE)
	strip builds/bin/pcvc4
	# some test cases fail (and are known to fail)
	-$(MAKE) check BINARY=pcvc4
	#$(MAKE) -C test/regress/regress1 check BINARY=pcvc4
	# package the parallel track zipfile
	mkdir -p cvc4-parallel-smtcomp-$(YEAR)
	cp -p builds/bin/pcvc4 cvc4-parallel-smtcomp-$(YEAR)/pcvc4
	mkdir cvc4-parallel-smtcomp-$(YEAR)/bin
	( echo '#!/bin/sh'; \
	  echo 'exec ./pcvc4 --threads 2 -L smt2 --no-checking --no-interactive' ) > cvc4-parallel-smtcomp-$(YEAR)/bin/starexec_run_default
	chmod 755 cvc4-parallel-smtcomp-$(YEAR)/bin/starexec_run_default
	#echo "CVC4 for SMT-COMP parallel track `builds/bin/cvc4 --version`" > cvc4-parallel-smtcomp-$(YEAR)/starexec_description.txt
	cd cvc4-parallel-smtcomp-$(YEAR) && zip -r ../cvc4-parallel-smtcomp-$(YEAR).zip *
