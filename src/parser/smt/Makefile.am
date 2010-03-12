AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libparsersmt.la

ANTLR_TOKEN_STUFF = \
	@srcdir@/generated/SmtVocabularyTokenTypes.hpp \
	@srcdir@/generated/SmtVocabularyTokenTypes.txt \
	@srcdir@/generated/AntlrSmtParserTokenTypes.hpp \
	@srcdir@/generated/AntlrSmtParserTokenTypes.txt
ANTLR_LEXER_STUFF = \
	@srcdir@/generated/AntlrSmtLexer.hpp \
	@srcdir@/generated/AntlrSmtLexer.cpp \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@srcdir@/generated/AntlrSmtParser.hpp \
	@srcdir@/generated/AntlrSmtParser.cpp
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsersmt_la_SOURCES = \
	smt_lexer.g \
	smt_parser.g \
	$(ANTLR_STUFF)

BUILT_SOURCES = $(ANTLR_STUFF)
dist-hook: $(ANTLR_STUFF)
MAINTAINERCLEANFILES = $(ANTLR_STUFF)
maintainer-clean-local:
	-rmdir @srcdir@/generated
	-rm -f @srcdir@/stamp-generated

@srcdir@/stamp-generated:
	mkdir -p @srcdir@/generated
	touch @srcdir@/stamp-generated
# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
@srcdir@/generated/AntlrSmtLexer.hpp: smt_lexer.g @srcdir@/stamp-generated
	$(AM_V_at)-rm -f $(ANTLR_LEXER_STUFF)
	$(AM_V_GEN)$(ANTLR) -o "@srcdir@/generated" "@srcdir@/smt_lexer.g"
@srcdir@/generated/AntlrSmtLexer.cpp $(ANTLR_TOKEN_STUFF): @srcdir@/generated/AntlrSmtLexer.hpp
# doesn't actually depend on the lexer, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@srcdir@/generated/AntlrSmtParser.hpp: smt_parser.g smt_lexer.g $(ANTLR_TOKEN_STUFF) @srcdir@/stamp-generated
	$(AM_V_at)-rm -f $(ANTLR_PARSER_STUFF)
	$(AM_V_GEN)$(ANTLR) -o "@srcdir@/generated" "@srcdir@/smt_parser.g"
@srcdir@/generated/AntlrSmtParser.cpp: @srcdir@/generated/AntlrSmtParser.hpp
