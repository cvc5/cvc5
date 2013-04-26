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
	-I@builddir@ -I@srcdir@/include -I@srcdir@
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = lib options expr util context theory prop decision smt printer proof . parser compat bindings main

lib_LTLIBRARIES = libcvc4.la
if HAVE_CXXTESTGEN
check_LTLIBRARIES = libcvc4_noinst.la
endif

libcvc4_la_LDFLAGS = -version-info $(LIBCVC4_VERSION)

# This "tricks" automake into linking us as a C++ library (rather than
# as a C library, which messes up exception handling support)
nodist_EXTRA_libcvc4_noinst_la_SOURCES = dummy.cpp
nodist_EXTRA_libcvc4_la_SOURCES = dummy.cpp
libcvc4_noinst_la_SOURCES = git_versioninfo.cpp svn_versioninfo.cpp
libcvc4_la_SOURCES = git_versioninfo.cpp svn_versioninfo.cpp
libcvc4_la_LIBADD = \
	@builddir@/options/liboptions.la \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/proof/libproof.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/prop/bvminisat/libbvminisat.la \
	@builddir@/printer/libprinter.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la \
	@builddir@/decision/libdecision.la
libcvc4_noinst_la_LIBADD = \
	@builddir@/options/liboptions.la \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/proof/libproof.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/prop/bvminisat/libbvminisat.la \
	@builddir@/printer/libprinter.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la \
	@builddir@/decision/libdecision.la

if CVC4_NEEDS_REPLACEMENT_FUNCTIONS
libcvc4_la_LIBADD += \
	@builddir@/lib/libreplacements.la
libcvc4_noinst_la_LIBADD += \
	@builddir@/lib/libreplacements.la
endif

if CVC4_USE_GLPK
libcvc4_la_LIBADD += $(GLPK_LIBS)
libcvc4_noinst_la_LIBADD += $(GLPK_LIBS)
endif

CLEANFILES = \
	svn_versioninfo.cpp \
	svninfo.tmp \
	svninfo \
	git_versioninfo.cpp \
	gitinfo.tmp \
	gitinfo

EXTRA_DIST = \
	include/cvc4_private_library.h \
	include/cvc4parser_private.h \
	include/cvc4parser_public.h \
	include/cvc4_private.h \
	include/cvc4_public.h \
	include/cvc4.h \
	cvc4.i

svn_versioninfo.cpp: svninfo
	$(AM_V_GEN)( \
	  if test -s svninfo; then \
	    issvn=true; \
	    branch=`grep '^URL: ' svninfo | sed 's,.*/cvc4/,,'`; \
	    rev=`grep '^Revision: ' svninfo | awk '{print$$2}'`; \
	    mods=`grep '^Modifications: ' svninfo | awk '{print$$2} END { if(!NR) print "false" }'`; \
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

git_versioninfo.cpp: gitinfo
	$(AM_V_GEN)( \
	  if test -s gitinfo; then \
	    isgit=true; \
	    branch=`head -1 gitinfo`; \
	    rev=`head -2 gitinfo | tail -1 | awk '{print$$1}'`; \
	    mods=`grep '^Modifications: ' gitinfo | awk '{print$$2} END { if(!NR) print "false" }'`; \
	  else \
	    isgit=false; \
	    branch=unknown; \
	    rev=unknown; \
	    mods=false; \
	  fi; \
	  echo "#include \"util/configuration.h\""; \
	  echo "const bool ::CVC4::Configuration::IS_GIT_BUILD = $$isgit;"; \
	  echo "const char* const ::CVC4::Configuration::GIT_BRANCH_NAME = \"$$branch\";"; \
	  echo "const char* const ::CVC4::Configuration::GIT_COMMIT = \"$$rev\";"; \
	  echo "const bool ::CVC4::Configuration::GIT_HAS_MODIFICATIONS = $$mods;"; \
	) >"$@"
# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
gitinfo: gitinfo.tmp
	$(AM_V_GEN)diff -q gitinfo.tmp gitinfo &>/dev/null || mv gitinfo.tmp gitinfo || true
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: gitinfo.tmp
gitinfo.tmp:
	$(AM_V_GEN)(cd "$(top_srcdir)"; if test -e .git/HEAD; then if ! grep -q '^ref: refs/heads/' .git/HEAD; then echo; fi; sed 's,^ref: refs/heads/,,' .git/HEAD; git show-ref refs/heads/`sed 's,^ref: refs/heads/,,' .git/HEAD`; echo "Modifications: `test -z \"\`git status -s -uno\`\" && echo false || echo true`"; fi) >"$@" 2>/dev/null || true

install-data-local:
	(echo include/cvc4.h; \
	 echo include/cvc4_public.h; \
	 echo include/cvc4parser_public.h; \
	 echo util/tls.h; \
	 echo util/integer.h; \
	 echo util/rational.h; \
	 find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|private_library\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		$(mkinstalldirs) "$$(dirname "$(DESTDIR)$(includedir)/cvc4/$$d")"; \
		if [ -e "$$f" ]; then \
			path="$$f"; \
			fixpath="$$f.fix"; \
		else \
			path="$(srcdir)/$$f"; \
			fixpath="$(builddir)/$$f.fix"; \
			$(MKDIR_P) "`dirname "$$fixpath"`"; \
		fi; \
		sed 's,^\([ \t]*#[ \t]*include[ \t*]\)"\(.*\)"\([ \t]*\)$$,\1<cvc4/\2>\3,' "$$path" > "$$fixpath" || exit 1; \
		echo $(INSTALL_DATA) "$$fixpath" "$(DESTDIR)$(includedir)/cvc4/$$d"; \
		$(INSTALL_DATA) "$$fixpath" "$(DESTDIR)$(includedir)/cvc4/$$d" || exit 1; \
	done

uninstall-local:
	-(echo include/cvc4.h; \
	  echo include/cvc4_public.h; \
	  echo include/cvc4parser_public.h; \
	  echo util/tls.h; \
	  echo util/integer.h; \
	  echo util/rational.h; \
	  find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|private_library\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		rm -f "$(DESTDIR)$(includedir)/cvc4/$$d"; \
	done
	-rmdir "$(DESTDIR)$(includedir)/cvc4/bindings/compat"
	-rmdir "$(DESTDIR)$(includedir)/cvc4/bindings"
	-rmdir "$(DESTDIR)$(includedir)/cvc4"
	-rmdir "$(DESTDIR)$(libdir)/ocaml/cvc4"

# clean up the .fix files
mostlyclean-local:
	(echo include/cvc4.h; \
	 echo include/cvc4_public.h; \
	 echo include/cvc4parser_public.h; \
	 echo util/tls.h; \
	 echo util/integer.h; \
	 echo util/rational.h; \
	 find * -name '*.h.fix' | \
		xargs grep -l '^# *include  *<cvc4/cvc4.*_public\.h>' | \
		sed 's,\.fix$$,,'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|private_library\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		if [ -e "$$f" ]; then \
			path="$$f"; \
			fixpath="$$f.fix"; \
		else \
			path="$(srcdir)/$$f"; \
			fixpath="$(builddir)/$$f.fix"; \
			$(MKDIR_P) "`dirname "$$fixpath"`"; \
		fi; \
		echo rm -f "$$fixpath"; \
		rm -f "$$fixpath"; \
	done

