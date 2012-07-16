AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libsmt.la

libsmt_la_SOURCES = \
	smt_engine.cpp \
	smt_engine.h \
	smt_engine_scope.cpp \
	smt_engine_scope.h \
	modal_exception.h \
	bad_option_exception.h \
	no_such_function_exception.h

EXTRA_DIST = \
	bad_option_exception.i \
	no_such_function_exception.i \
	modal_exception.i \
	smt_engine.i
