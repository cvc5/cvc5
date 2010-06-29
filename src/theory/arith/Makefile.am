AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith_type_rules.h \
	arith_rewriter.h \
	arith_rewriter.cpp \
	arith_utilities.h \
	arith_constants.h \
	arith_activity.h \
	delta_rational.h \
	delta_rational.cpp \
	partial_model.h \
	partial_model.cpp \
	ordered_bounds_list.h \
	basic.h \
	normal.h \
	slack.h \
	tableau.h \
	arith_propagator.h \
	arith_propagator.cpp \
	theory_arith.h \
	theory_arith.cpp

EXTRA_DIST = kinds
