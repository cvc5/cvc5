AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libuf.la

libuf_la_SOURCES = \
	theory_uf.h \
	theory_uf.cpp \
	theory_uf_type_rules.h \
	theory_uf_rewriter.h \
	equality_engine.h \
	equality_engine_types.h \
	equality_engine.cpp \
	symmetry_breaker.h \
	symmetry_breaker.cpp

EXTRA_DIST = kinds
