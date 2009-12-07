INCLUDES = -I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

noinst_LTLIBRARIES = libparsersmt.la

libparsersmt_la_SOURCES = \
	SmtLexer.g \
	SmtParser.g \
	AntlrSmtLexer.hpp \
	AntlrSmtLexer.cpp \
	AntlrSmtParser.hpp \
	AntlrSmtParser.cpp 

BUILT_SOURCES = \
	AntlrSmtLexer.hpp \
	AntlrSmtLexer.cpp \
	AntlrSmtParser.hpp \
	AntlrSmtParser.cpp 
CLEAN_FILES = $(BUILT_SOURCES)

AntlrSmtLexer.cpp AntlrSmtLexer.hpp: SmtLexer.g
	$(ANTLR) -o "@builddir@" "@srcdir@/SmtLexer.g"

AntlrSmtParser.cpp AntlrSmtParser.hpp: SmtParser.g
	$(ANTLR) -o "@builddir@" "@srcdir@/SmtParser.g"
