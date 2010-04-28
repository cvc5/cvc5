AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith.h \
	theory_arith.cpp \
	arith_rewriter.h \
	arith_rewriter.cpp \
	arith_utilities.h \
	arith_constants.h \
	basic.h \
	normal.h \
	slack.h \
	tableau.h

EXTRA_DIST = kinds
