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
	no_such_function_exception.h \
	simplification_mode.h \
	simplification_mode.cpp

nodist_libsmt_la_SOURCES = \
	smt_options.cpp

EXTRA_DIST = \
	options_handlers.h \
	smt_options_template.cpp \
	no_such_function_exception.i \
	modal_exception.i \
	smt_engine.i
