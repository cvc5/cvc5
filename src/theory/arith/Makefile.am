AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -wunknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith_type_rules.h \
	arith_rewriter.h \
	arith_rewriter.cpp \
	arith_utilities.h \
	arith_constants.h \
	delta_rational.h \
	delta_rational.cpp \
	partial_model.h \
	partial_model.cpp \
	basic.h \
	normal.h \
	slack.h \
	tableau.h \
	theory_arith.h \
	theory_arith.cpp

EXTRA_DIST = kinds
