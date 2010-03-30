AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../../include -I@srcdir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -fvisibility=hidden
# Compile generated C files using C++ compiler
CC=$(CXX)

noinst_LTLIBRARIES = libparsercvc.la

ANTLR_TOKEN_STUFF = \
	@srcdir@/generated/Cvc.tokens
ANTLR_LEXER_STUFF = \
    @srcdir@/generated/CvcLexer.h \
    @srcdir@/generated/CvcLexer.c \
    $(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
    @srcdir@/generated/CvcParser.h \
    @srcdir@/generated/CvcParser.c
ANTLR_STUFF = \
    $(ANTLR_LEXER_STUFF) \
    $(ANTLR_PARSER_STUFF)

libparsercvc_la_SOURCES = \
    Cvc.g \
    cvc_input.h \
    cvc_input.cpp \
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
@srcdir@/generated/CvcLexer.h: Cvc.g @srcdir@/stamp-generated
	-rm -f $(ANTLR_STUFF)
	$(ANTLR) -o "@srcdir@/generated" "@srcdir@/Cvc.g"

# These don't actually depend on CvcLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@srcdir@/generated/CvcLexer.c @srcdir@/generated/CvcParser.h @srcdir@/generated/CvcParser.c $(ANTLR_TOKEN_STUFF): @srcdir@/generated/CvcLexer.h
