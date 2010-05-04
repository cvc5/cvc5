AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbv.la

libbv_la_SOURCES = \
	theory_bv.h \
	theory_bv_type_rules.h

EXTRA_DIST = kinds
