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

AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../include -I@srcdir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -fvisibility=hidden

SUBDIRS = smt cvc

nobase_lib_LTLIBRARIES = libcvc4parser.la
noinst_LTLIBRARIES = libcvc4parser_noinst.la

libcvc4parser_la_LDFLAGS = $(ANTLR_LDFLAGS)
libcvc4parser_la_LIBADD = libcvc4parser_noinst.la
libcvc4parser_la_LINK = $(CXXLINK)

libcvc4parser_noinst_la_LDFLAGS = $(ANTLR_LDFLAGS)
libcvc4parser_noinst_la_LIBADD = \
	@builddir@/smt/libparsersmt.la \
	@builddir@/cvc/libparsercvc.la

libcvc4parser_la_SOURCES =
libcvc4parser_noinst_la_SOURCES = \
	parser.h \
	parser.cpp \
	parser_exception.h \
	symbol_table.h \
	antlr_parser.h \
	antlr_parser.cpp
