# LIBCVC4PARSER_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
LIBCVC4PARSER_VERSION = @CVC4_PARSER_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@builddir@/.. $(ANTLR_INCLUDES) -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = smt1 smt2 cvc tptp

lib_LTLIBRARIES = libcvc4parser.la

libcvc4parser_la_LDFLAGS = $(ANTLR_LDFLAGS) \
	-version-info $(LIBCVC4PARSER_VERSION)

libcvc4parser_la_LIBADD = \
	@builddir@/smt1/libparsersmt1.la \
	@builddir@/smt2/libparsersmt2.la \
	@builddir@/tptp/libparsertptp.la \
	@builddir@/cvc/libparsercvc.la \
	@builddir@/../libcvc4.la \
	@builddir@/../lib/libreplacements.la

libcvc4parser_la_SOURCES = \
	antlr_input.cpp \
	antlr_input.h \
	antlr_input_imports.cpp \
	antlr_line_buffered_input.cpp \
	antlr_line_buffered_input.h \
	antlr_tracing.h \
	antlr_undefines.h \
	bounded_token_buffer.cpp \
	bounded_token_buffer.h \
	bounded_token_factory.cpp \
	bounded_token_factory.h \
	input.cpp \
	input.h \
	memory_mapped_input_buffer.cpp \
	memory_mapped_input_buffer.h \
	parser.cpp \
	parser.h \
	parser_builder.cpp \
	parser_builder.h \
	parser_exception.h

EXTRA_DIST = \
	Makefile.antlr_tracing \
	cvc4parser.i \
	input.i \
	parser_builder.i \
	parser_exception.i \
	parser.i
