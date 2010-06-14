AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarrays.la

libarrays_la_SOURCES = \
	theory_arrays.h \
	theory_arrays.cpp

EXTRA_DIST = kinds
