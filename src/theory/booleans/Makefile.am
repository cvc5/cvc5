AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbooleans.la

libbooleans_la_SOURCES = \
	type_enumerator.h \
	theory_bool.h \
	theory_bool.cpp \
	theory_bool_type_rules.h \
	theory_bool_rewriter.h \
	theory_bool_rewriter.cpp \
	circuit_propagator.h \
	circuit_propagator.cpp \
	boolean_term_conversion_mode.h \
	boolean_term_conversion_mode.cpp

EXTRA_DIST = \
	kinds \
	options_handlers.h
