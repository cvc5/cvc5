#  -*-makefile-*-
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
.PHONY: submission submission-main submission-application submission-parallel
submission:
	@if [ -d builds-smtcomp ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: remove the builds-smtcomp directory' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	@if test -d cvc4-smtcomp-$(YEAR) || test -e cvc4-smtcomp-$(YEAR).zip || \
	    test -d cvc4-smtcomp-main-$(YEAR) || test -e cvc4-smtcomp-main-$(YEAR).zip || \
	    test -d cvc4-smtcomp-application-$(YEAR) || test -e cvc4-smtcomp-application-$(YEAR).zip || \
	    test -d cvc4-smtcomp-parallel-$(YEAR) || test -e cvc4-smtcomp-parallel-$(YEAR).zip; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove cvc4-smtcomp*-$(YEAR) and corresponding zipfiles.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	$(MAKE) submission-main
	$(MAKE) submission-application
	$(MAKE) submission-parallel
	mkdir -p cvc4-smtcomp-$(YEAR)/bin
	cp -p cvc4-smtcomp-main-$(YEAR)/bin/cvc4 cvc4-smtcomp-$(YEAR)/bin/cvc4-main
	cp -p cvc4-smtcomp-main-$(YEAR)/bin/starexec_run_default cvc4-smtcomp-$(YEAR)/bin/starexec_run_default
	cp -p cvc4-smtcomp-application-$(YEAR)/bin/cvc4 cvc4-smtcomp-$(YEAR)/bin/cvc4-application
	cp -p cvc4-smtcomp-application-$(YEAR)/bin/starexec_run_default cvc4-smtcomp-$(YEAR)/bin/starexec_run_application
	cp -p cvc4-smtcomp-parallel-$(YEAR)/bin/pcvc4 cvc4-smtcomp-$(YEAR)/bin/pcvc4
	#cp -p cvc4-smtcomp-parallel-$(YEAR)/bin/starexec_run_default cvc4-smtcomp-$(YEAR)/bin/starexec_run_parallel
	cat cvc4-smtcomp-main-$(YEAR)/starexec_description.txt \
	    cvc4-smtcomp-application-$(YEAR)/starexec_description.txt \
	    cvc4-smtcomp-parallel-$(YEAR)/starexec_description.txt \
	    > cvc4-smtcomp-$(YEAR)/starexec_description.txt
	perl -pi -e 's,/cvc4\b,/cvc4-main,g' cvc4-smtcomp-$(YEAR)/bin/starexec_run_default
	perl -pi -e 's,/cvc4\b,/cvc4-application,g' cvc4-smtcomp-$(YEAR)/bin/starexec_run_application
	cd cvc4-smtcomp-$(YEAR) && zip -r ../cvc4-smtcomp-$(YEAR).zip *
submission-main:
	@if [ -d builds-smtcomp/main ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove the builds-smtcomp/main directory' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	@if [ -e contrib/run-script-smtcomp$(YEAR) ]; then :; else \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Expected contrib/run-script-smtcomp$(YEAR) to exist!' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	@if test -d cvc4-smtcomp-main-$(YEAR) || test -e cvc4-smtcomp-main-$(YEAR).zip; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove cvc4-smtcomp-main-$(YEAR) and cvc4-smtcomp-main-$(YEAR).zip first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	./autogen.sh
	mkdir -p builds-smtcomp/main
	( cd builds-smtcomp/main; \
	  ../../configure competition --disable-thread-support --disable-shared --enable-static-binary --with-cln --with-glpk --with-abc --without-readline --enable-gpl; \
	  $(MAKE) V=1; \
	  strip src/main/cvc4; \
	  $(MAKE) check )
	# main track
	mkdir -p cvc4-smtcomp-main-$(YEAR)/bin
	cp -p builds-smtcomp/main/src/main/cvc4 cvc4-smtcomp-main-$(YEAR)/bin/cvc4
	cp contrib/run-script-smtcomp$(YEAR) cvc4-smtcomp-main-$(YEAR)/bin/starexec_run_default
	chmod 755 cvc4-smtcomp-main-$(YEAR)/bin/starexec_run_default
	echo "CVC4 for SMT_COMP main track `builds-smtcomp/main/src/main/cvc4 --version | head -1 | sed 's,.*version ,,;s,-,_,g;s,[^a-zA-Z0-9. _],,g'`" > cvc4-smtcomp-main-$(YEAR)/starexec_description.txt
	cd cvc4-smtcomp-main-$(YEAR) && zip -r ../cvc4-smtcomp-main-$(YEAR).zip *
submission-application:
	# application track is a separate build because it has different preprocessor #defines
	@if [ -d builds-smtcomp/application ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove the builds-smtcomp/application directory' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	@if test -d cvc4-smtcomp-application-$(YEAR) || test -e cvc4-smtcomp-application-$(YEAR).zip; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove cvc4-smtcomp-application-$(YEAR) and cvc4-smtcomp-application-$(YEAR).zip first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	@if [ -e contrib/run-script-smtcomp$(YEAR)-application ]; then :; else \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Expected contrib/run-script-smtcomp$(YEAR)-application to exist!' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	./autogen.sh
	mkdir -p builds-smtcomp/application
	( cd builds-smtcomp/application; \
	  ../../configure competition --disable-thread-support --disable-shared --enable-static-binary --with-cln --without-glpk --with-abc --without-readline --enable-gpl CXXFLAGS=-DCVC4_SMTCOMP_APPLICATION_TRACK CFLAGS=-DCVC4_SMTCOMP_APPLICATION_TRACK; \
	  $(MAKE) V=1; \
	  strip src/main/cvc4; \
	  $(MAKE) check )
	# package the application track zipfile
	mkdir -p cvc4-smtcomp-application-$(YEAR)/bin
	cp -p builds-smtcomp/application/src/main/cvc4 cvc4-smtcomp-application-$(YEAR)/bin/cvc4
	cp contrib/run-script-smtcomp$(YEAR)-application cvc4-smtcomp-application-$(YEAR)/bin/starexec_run_default
	chmod 755 cvc4-smtcomp-application-$(YEAR)/bin/starexec_run_default
	echo "CVC4 for SMT_COMP application track `builds-smtcomp/application/src/main/cvc4 --version | head -1 | sed 's,.*version ,,;s,-,_,g;s,[^a-zA-Z0-9. _],,g'`" > cvc4-smtcomp-application-$(YEAR)/starexec_description.txt
	cd cvc4-smtcomp-application-$(YEAR) && zip -r ../cvc4-smtcomp-application-$(YEAR).zip *
submission-parallel:
	# parallel track can't be built with -cln, so it's a separate build
	@if [ -d builds-smtcomp/parallel ]; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove the builds-smtcomp/parallel directory' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	@if test -d cvc4-smtcomp-parallel-$(YEAR) || test -e cvc4-smtcomp-parallel-$(YEAR).zip; then \
	  echo 'ERROR:' >&2; \
	  echo 'ERROR: Please remove cvc4-smtcomp-parallel-$(YEAR) and cvc4-smtcomp-parallel-$(YEAR).zip first.' >&2; \
	  echo 'ERROR:' >&2; \
	  exit 1; \
	fi
	./autogen.sh
	mkdir -p builds-smtcomp/parallel
	( cd builds-smtcomp/parallel; \
	  ../../configure competition --disable-shared --enable-static-binary --with-gmp --with-portfolio --with-glpk --with-abc --without-readline --enable-gpl; \
	  $(MAKE) V=1; \
	  strip src/main/pcvc4; \
	  $(MAKE) check BINARY=pcvc4 CVC4_REGRESSION_ARGS=--fallback-sequential || true )
	# package the parallel track zipfile
	mkdir -p cvc4-smtcomp-parallel-$(YEAR)/bin
	cp -p builds-smtcomp/parallel/src/main/pcvc4 cvc4-smtcomp-parallel-$(YEAR)/bin/pcvc4
	( echo '#!/bin/sh'; \
	  echo 'exec ./pcvc4 --threads 2 -L smt2 --no-checking --no-interactive --no-wait-to-join "$@"' ) > cvc4-smtcomp-parallel-$(YEAR)/bin/starexec_run_default
	chmod 755 cvc4-smtcomp-parallel-$(YEAR)/bin/starexec_run_default
	echo "CVC4 for SMT_COMP parallel track `builds-smtcomp/parallel/src/main/pcvc4 --version | head -1 | sed 's,.*version ,,;s,-,_,g;s,[^a-zA-Z0-9. _],,g'`" > cvc4-smtcomp-parallel-$(YEAR)/starexec_description.txt
	cd cvc4-smtcomp-parallel-$(YEAR) && zip -r ../cvc4-smtcomp-parallel-$(YEAR).zip *
