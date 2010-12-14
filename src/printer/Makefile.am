AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libprinter.la

libprinter_la_SOURCES = \
	printer.h \
	printer.cpp \
	ast/ast_printer.h \
	ast/ast_printer.cpp \
	smt/smt_printer.h \
	smt/smt_printer.cpp \
	smt2/smt2_printer.h \
	smt2/smt2_printer.cpp \
	cvc/cvc_printer.h \
	cvc/cvc_printer.cpp
