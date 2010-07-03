AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbuiltin.la

libbuiltin_la_SOURCES = \
	theory_builtin_type_rules.h \
	theory_builtin.h \
	theory_builtin.cpp

EXTRA_DIST = kinds
