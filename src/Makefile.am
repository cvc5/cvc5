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

SUBDIRS = lib expr util context theory prop smt . parser main

lib_LTLIBRARIES = libcvc4.la
noinst_LTLIBRARIES = libcvc4_noinst.la

libcvc4_la_LDFLAGS = -version-info $(LIBCVC4_VERSION)

# empty.cpp is a fake file added to "trick" automake into linking us as a
# C++ library (rather than as a C library, which messes up exception
# handling support)
libcvc4_la_SOURCES = empty.cpp
libcvc4_noinst_la_SOURCES = empty.cpp
libcvc4_la_LIBADD = \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la \
	@builddir@/lib/libreplacements.la
libcvc4_noinst_la_LIBADD = \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la \
	@builddir@/lib/libreplacements.la

EXTRA_DIST = \
	include/cvc4parser_private.h \
	include/cvc4parser_public.h \
	include/cvc4_private.h \
	include/cvc4_public.h

# empty.cpp hack; see above
empty.cpp:; touch empty.cpp

publicheaders = \
	include/cvc4_public.h \
	include/cvc4parser_public.h

install-data-local: $(publicheaders)
	$(mkinstalldirs) $(DESTDIR)$(prefix)$(includedir)/cvc4
	@for f in $(publicheaders); do \
		echo $(INSTALL_DATA) "$(srcdir)/$$f" "$(DESTDIR)$(prefix)$(includedir)/cvc4"; \
		$(INSTALL_DATA) "$(srcdir)/$$f" "$(DESTDIR)$(prefix)$(includedir)/cvc4"; \
	done

uninstall-local:
	@for f in $(publicheaders); do \
		f=`echo "$$f" | sed 's,.*/,,'`; \
		rm -f "$(DESTDIR)$(prefix)$(includedir)/cvc4/$$f"; \
	done
	@rmdir "$(DESTDIR)$(prefix)$(includedir)/cvc4"
