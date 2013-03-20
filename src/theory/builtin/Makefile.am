AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbuiltin.la

libbuiltin_la_SOURCES = \
	theory_builtin_type_rules.h \
	type_enumerator.h \
	theory_builtin_rewriter.h \
	theory_builtin_rewriter.cpp \
	theory_builtin.h \
	theory_builtin.cpp

EXTRA_DIST = \
	kinds
