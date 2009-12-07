INCLUDES = -I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

noinst_LTLIBRARIES = libparsercvc.la

libparsercvc_la_SOURCES = \
	CvcLexer.g \
	CvcParser.g \
	AntlrCvcLexer.hpp \
	AntlrCvcLexer.cpp \
	AntlrCvcParser.hpp \
	AntlrCvcParser.cpp   

BUILT_SOURCES = \
	AntlrCvcLexer.hpp \
	AntlrCvcLexer.cpp \
	AntlrCvcParser.hpp \
	AntlrCvcParser.cpp 


AntlrCvcLexer.hpp: CvcLexer.g
AntlrCvcLexer.cpp: CvcLexer.g
	$(ANTLR) @srcdir@/CvcLexer.g

AntlrCvcParser.hpp: CvcParser.g AntlrCvcLexer.cpp
AntlrCvcParser.cpp: CvcParser.g AntlrCvcLexer.cpp
	$(ANTLR) @srcdir@/CvcParser.g
