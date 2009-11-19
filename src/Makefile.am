INCLUDES = -I@srcdir@/include -I@srcdir@
AM_CXXFLAGS = -Wall -fvisibility=hidden

SUBDIRS = util expr context prop smt theory parser main

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_LIBADD = \
	util/libutil.a \
	expr/libexpr.a \
	context/libcontext.a \
	prop/minisat/libminisat.a \
	smt/libsmt.a \
	theory/libtheory.a \
	parser/libparser.a

EXTRA_DIST = \
	include/cvc4.h \
	include/cvc4_expr.h
