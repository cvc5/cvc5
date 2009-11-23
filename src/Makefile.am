INCLUDES = -I@srcdir@/include -I@srcdir@
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4LIB

SUBDIRS = util expr context prop smt theory . parser main

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_SOURCES =
libcvc4_la_LIBADD = \
	util/libutil.la \
	expr/libexpr.la \
	context/libcontext.la \
	prop/libprop.la \
	prop/minisat/libminisat.la \
	smt/libsmt.la \
	theory/libtheory.la

publicheaders = \
	include/cvc4.h \
	include/cvc4_config.h \
	include/cvc4_expr.h

install-data-local:
	$(mkinstalldirs) $(DESTDIR)$(includedir)/cvc4; \
	@for f in $(publicheaders); do
		echo $(INSTALL_DATA) "$(srcdir)/$$f" "$(DESTDIR)/$(includedir)/cvc4"
		$(INSTALL_DATA) "$(srcdir)/$$f" "$(DESTDIR)/$(includedir)/cvc4"
	done
