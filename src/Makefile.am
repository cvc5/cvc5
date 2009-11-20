INCLUDES = -I@srcdir@/include -I@srcdir@
AM_CXXFLAGS = -Wall -fvisibility=hidden

SUBDIRS = util expr context prop smt theory . parser main

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_SOURCES =
libcvc4_la_LIBADD = \
	util/libutil.la \
	expr/libexpr.la \
	context/libcontext.la \
	prop/minisat/libminisat.la \
	smt/libsmt.la \
	theory/libtheory.la

EXTRA_DIST = \
	include/cvc4.h \
	include/cvc4_expr.h
