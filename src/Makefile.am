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

AM_CPPFLAGS =
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/include -I@srcdir@
AM_CXXFLAGS = -Wall -fvisibility=hidden

SUBDIRS = expr util context prop smt theory . parser main

lib_LTLIBRARIES = libcvc4.la

noinst_LTLIBRARIES = libcvc4_noinst.la

libcvc4_la_LDFLAGS = -version-info $(LIBCVC4_VERSION)
libcvc4_la_LINK = $(CXXLINK)

libcvc4_la_SOURCES =
libcvc4_la_LIBADD = libcvc4_noinst.la

# empty.cpp is a fake file added to "trick" automake into linking us as a
# C++ library (rather than as a C library, which messes up exception
# handling support)
libcvc4_noinst_la_SOURCES = empty.cpp
libcvc4_noinst_la_LIBADD = \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/context/libcontext.la \
	@builddir@/prop/libprop.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/smt/libsmt.la \
	@builddir@/theory/libtheory.la

# empty.cpp hack; see above
empty.cpp:; touch empty.cpp

publicheaders = \
	include/cvc4_config.h

install-data-local: $(publicheaders)
	$(mkinstalldirs) $(DESTDIR)$(includedir)/cvc4
	@for f in $(publicheaders); do \
		echo $(INSTALL_DATA) "$(srcdir)/$$f" "$(DESTDIR)/$(includedir)/cvc4"; \
		$(INSTALL_DATA) "$(srcdir)/$$f" "$(DESTDIR)/$(includedir)/cvc4"; \
	done

include/cvc4.h: smt/smt_engine.h
	@srcdir@/headergen.pl $< $@
include/cvc4_expr.h: expr/expr.h
