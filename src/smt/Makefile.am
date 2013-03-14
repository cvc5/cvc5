AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libsmt.la

libsmt_la_SOURCES = \
	smt_engine.cpp \
	smt_engine.h \
	model_postprocessor.cpp \
	model_postprocessor.h \
	smt_engine_scope.cpp \
	smt_engine_scope.h \
	command_list.cpp \
	command_list.h \
	modal_exception.h \
	boolean_terms.h \
	boolean_terms.cpp \
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
