AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarrays.la

libarrays_la_SOURCES = \
	theory_arrays_type_rules.h \
	theory_arrays_rewriter.h \
	theory_arrays.h \
	theory_arrays.cpp

EXTRA_DIST = kinds
