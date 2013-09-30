AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libprinter.la

libprinter_la_SOURCES = \
	printer.h \
	printer.cpp \
	dagification_visitor.h \
	dagification_visitor.cpp \
	model_format_mode.h \
	model_format_mode.cpp \
	ast/ast_printer.h \
	ast/ast_printer.cpp \
	smt1/smt1_printer.h \
	smt1/smt1_printer.cpp \
	smt2/smt2_printer.h \
	smt2/smt2_printer.cpp \
	cvc/cvc_printer.h \
	cvc/cvc_printer.cpp \
	tptp/tptp_printer.h \
	tptp/tptp_printer.cpp

EXTRA_DIST = \
	options_handlers.h
