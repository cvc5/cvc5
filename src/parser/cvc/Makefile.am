INCLUDES = -I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

noinst_LTLIBRARIES = libparsercvc.la

ANTLR_STUFF = \
	AntlrCvcLexer.hpp \
	AntlrCvcLexer.cpp \
	AntlrCvcParser.hpp \
	AntlrCvcParser.cpp 

libparsercvc_la_SOURCES = \
	CvcLexer.g \
	CvcParser.g \
	$(ANTLR_STUFF)

BUILT_SOURCES = $(ANTLR_STUFF)
CLEAN_FILES = $(ANTLR_STUFF)

AntlrCvcLexer.cpp: CvcLexer.g
	$(ANTLR) -o "@builddir@" "$<"
AntlrCvcParser.cpp: CvcParser.g CvcVocabularyTokenTypes.hpp CvcVocabularyTokenTypes.txt
	$(ANTLR) -o "@builddir@" "$<"
AntlrCvcLexer.hpp CvcVocabularyTokenTypes.hpp CvcVocabularyTokenTypes.txt: AntlrCvcLexer.cpp
AntlrCvcParser.hpp: AntlrCvcParser.cpp
