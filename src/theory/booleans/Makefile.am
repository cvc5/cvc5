AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -wunknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbooleans.la

libbooleans_la_SOURCES = \
	theory_bool.h \
	theory_bool_type_rules.h

EXTRA_DIST = kinds
