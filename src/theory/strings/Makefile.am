AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libstrings.la

libstrings_la_SOURCES = \
	theory_strings.h \
	theory_strings.cpp \
	theory_strings_rewriter.h \
	theory_strings_type_rules.h

EXTRA_DIST = \
	kinds
