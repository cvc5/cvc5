# LIBCVC4_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
LIBCVC4_VERSION = @CVC4_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/include -I@srcdir@ -I@builddir@
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = lib expr util context theory prop smt printer proof . parser compat bindings main

lib_LTLIBRARIES = libcvc4.la
if HAVE_CXXTESTGEN
check_LTLIBRARIES = libcvc4_noinst.la
endif

libcvc4_la_LDFLAGS = -version-info $(LIBCVC4_VERSION)

# This "tricks" automake into linking us as a C++ library (rather than
# as a C library, which messes up exception handling support)
nodist_EXTRA_libcvc4_noinst_la_SOURCES = dummy.cpp
nodist_EXTRA_libcvc4_la_SOURCES = dummy.cpp
libcvc4_noinst_la_SOURCES = subversion_versioninfo.cpp
libcvc4_la_SOURCES = subversion_versioninfo.cpp
libcvc4_la_LIBADD = \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/proof/libproof.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/printer/libprinter.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la \
	@builddir@/lib/libreplacements.la
libcvc4_noinst_la_LIBADD = \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/proof/libproof.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/printer/libprinter.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la \
	@builddir@/lib/libreplacements.la

CLEANFILES = \
	subversion_versioninfo.cpp \
	svninfo.tmp \
	svninfo

EXTRA_DIST = \
	include/cvc4parser_private.h \
	include/cvc4parser_public.h \
	include/cvc4_private.h \
	include/cvc4_public.h \
	include/cvc4.h \
	cvc4.i

subversion_versioninfo.cpp: svninfo
	$(AM_V_GEN)( \
	  if test -s svninfo; then \
	    issvn=true; \
	    branch=`grep '^URL: ' svninfo | sed 's,.*/cvc4/,,'`; \
	    rev=`grep '^Revision: ' svninfo | awk '{print$$2}'`; \
	    mods=`grep '^Modifications: ' svninfo | awk '{print$$2}'`; \
	  else \
	    issvn=false; \
	    branch=unknown; \
	    rev=0; \
	    mods=false; \
	  fi; \
	  echo "#include \"util/configuration.h\""; \
	  echo "const bool ::CVC4::Configuration::IS_SUBVERSION_BUILD = $$issvn;"; \
	  echo "const char* const ::CVC4::Configuration::SUBVERSION_BRANCH_NAME = \"$$branch\";"; \
	  echo "const unsigned ::CVC4::Configuration::SUBVERSION_REVISION = $$rev;"; \
	  echo "const bool ::CVC4::Configuration::SUBVERSION_HAS_MODIFICATIONS = $$mods;"; \
	) >"$@"
# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
svninfo: svninfo.tmp
	$(AM_V_GEN)diff -q svninfo.tmp svninfo &>/dev/null || mv svninfo.tmp svninfo || true
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: svninfo.tmp
svninfo.tmp:
	$(AM_V_GEN)(cd "$(top_srcdir)" && svn info && echo "Modifications: `test -z \"\`svn status -q\`\" && echo false || echo true`") >"$@" 2>/dev/null || true

install-data-local:
	(echo include/cvc4.h; \
	 echo include/cvc4_public.h; \
	 find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		$(mkinstalldirs) "$$(dirname "$(DESTDIR)$(includedir)/cvc4/$$d")"; \
		if [ -e "$$f" ]; then \
			path="$$f"; \
		else \
			path="$(srcdir)/$$f"; \
		fi; \
		echo $(INSTALL_DATA) "$$path" "$(DESTDIR)$(includedir)/cvc4/$$d"; \
		$(INSTALL_DATA) "$$path" "$(DESTDIR)$(includedir)/cvc4/$$d"; \
	done

uninstall-local:
	-(echo include/cvc4.h; \
	  echo include/cvc4_public.h; \
	  find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		rm -f "$(DESTDIR)$(includedir)/cvc4/$$d"; \
		rmdir -p "$$(dirname "$(DESTDIR)$(includedir)/cvc4/$$d")" 2>/dev/null; \
	done
	-rmdir "$(DESTDIR)$(includedir)/cvc4"
