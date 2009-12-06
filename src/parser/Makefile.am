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
# LIBCVC4PARSER_RELEASE (-release) should match the CVC4 release version
#
LIBCVC4PARSER_RELEASE = @CVC4_LIBRARY_RELEASE_CODE@
LIBCVC4PARSER_VERSION = @CVC4_PARSER_LIBRARY_VERSION@

INCLUDES = -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

SUBDIRS = smt

nobase_lib_LTLIBRARIES = libcvc4parser.la

libcvc4parser_la_LDFLAGS = $(ANTLR_LDFLAGS)
libcvc4parser_la_LIBADD = \
	@builddir@/smt/libparsersmt.la

libcvc4parser_la_SOURCES = \
	parser.h \
	parser.cpp \
	symbol_table.h \
	antlr_parser.h \
	antlr_parser.cpp

