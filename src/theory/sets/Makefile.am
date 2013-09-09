AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libsets.la

libsets_la_SOURCES = \
	theory_sets.h \
	theory_sets.cpp \
	theory_sets_private.h \
	theory_sets_private.cpp \
	theory_sets_rewriter.h \
	theory_sets_rewriter.cpp \
	theory_sets_type_rules.h \
	theory_set_type_enumerator.h

EXTRA_DIST = \
	kinds \
	options_handlers.h
