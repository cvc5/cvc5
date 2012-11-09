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
	command_list.cpp \
	command_list.h \
	modal_exception.h \
	logic_exception.h \
	simplification_mode.h \
	simplification_mode.cpp

nodist_libsmt_la_SOURCES = \
	smt_options.cpp

EXTRA_DIST = \
	options_handlers.h \
	smt_options_template.cpp \
	modal_exception.i \
	logic_exception.i \
	smt_engine.i
