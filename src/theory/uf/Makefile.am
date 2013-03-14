AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
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
	symmetry_breaker.cpp \
	theory_uf_strong_solver.h \
	theory_uf_strong_solver.cpp \
	theory_uf_model.h \
	theory_uf_model.cpp 

EXTRA_DIST = \
	kinds \
	options_handlers.h
