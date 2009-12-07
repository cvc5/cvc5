INCLUDES = -I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

noinst_LTLIBRARIES = libparsersmt.la

ANTLR_STUFF = \
	AntlrSmtLexer.hpp \
	AntlrSmtLexer.cpp \
	AntlrSmtParser.hpp \
	AntlrSmtParser.cpp 

libparsersmt_la_SOURCES = \
	SmtLexer.g \
	SmtParser.g \
	$(ANTLR_STUFF)

BUILT_SOURCES = $(ANTLR_STUFF)
CLEAN_FILES = $(ANTLR_STUFF)

AntlrSmtLexer.cpp AntlrSmtLexer.hpp: SmtLexer.g
	$(ANTLR) -o "@builddir@" "$<"
AntlrSmtParser.cpp AntlrSmtParser.hpp: SmtParser.g
	$(ANTLR) -o "@builddir@" "$<"
