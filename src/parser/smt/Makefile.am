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


AntlrSmtLexer.hpp: SmtLexer.g
AntlrSmtLexer.cpp: SmtLexer.g
	$(ANTLR) @srcdir@/SmtLexer.g

AntlrSmtParser.hpp: SmtParser.g AntlrSmtLexer.cpp
AntlrSmtParser.cpp: SmtParser.g AntlrSmtLexer.cpp
	$(ANTLR) @srcdir@/SmtParser.g
