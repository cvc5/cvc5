INCLUDES = -I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

noinst_LTLIBRARIES = libparsercvc.la

ANTLR_TOKEN_STUFF = \
	@srcdir@/generated/CvcVocabularyTokenTypes.hpp \
	@srcdir@/generated/CvcVocabularyTokenTypes.txt \
	@srcdir@/generated/AntlrCvcParserTokenTypes.hpp \
	@srcdir@/generated/AntlrCvcParserTokenTypes.txt
ANTLR_LEXER_STUFF = \
	@srcdir@/generated/AntlrCvcLexer.hpp \
	@srcdir@/generated/AntlrCvcLexer.cpp \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@srcdir@/generated/AntlrCvcParser.hpp \
	@srcdir@/generated/AntlrCvcParser.cpp
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsercvc_la_SOURCES = \
	CvcLexer.g \
	CvcParser.g \
	$(ANTLR_STUFF)

BUILT_SOURCES = $(ANTLR_STUFF)
dist-hook: $(ANTLR_STUFF)
MAINTAINERCLEANFILES = $(ANTLR_STUFF)
maintainerclean-local:
	-rmdir @srcdir@/generated
	-rm -f @srcdir@/stamp-generated

@srcdir@/stamp-generated:
	mkdir -p @srcdir@/generated
	touch @srcdir@/stamp-generated
# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
$(ANTLR_LEXER_STUFF): CvcLexer.g @srcdir@/generated
	-rm -f $(ANTLR_LEXER_STUFF)
	$(ANTLR) -o "@srcdir@/generated" "@srcdir@/CvcLexer.g"
# doesn't actually depend on the lexer, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
$(ANTLR_PARSER_STUFF): CvcParser.g CvcLexer.g $(ANTLR_TOKEN_STUFF) @srcdir@/generated
	-rm -f $(ANTLR_PARSER_STUFF)
	$(ANTLR) -o "@srcdir@/generated" "@srcdir@/CvcParser.g"
