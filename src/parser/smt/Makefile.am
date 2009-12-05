INCLUDES = -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

noinst_LTLIBRARIES = libparsersmt.la

libparsersmt_la_SOURCES = \
	SmtLexer.g \
	SmtParser.g \
	SmtLexer.hpp \
	SmtLexer.cpp \
	SmtParser.hpp \
	SmtParser.cpp   

BUILT_SOURCES = \
	SmtLexer.hpp \
	SmtLexer.cpp \
	SmtParser.hpp \
	SmtParser.cpp 

SmtLexer.cpp SmtLexer.hpp: SmtLexer.g
	$(ANTLR) @srcdir@/SmtLexer.g

SmtParser.cpp SmtParser.hpp: SmtParser.g
	$(ANTLR) @srcdir@/SmtParser.g
