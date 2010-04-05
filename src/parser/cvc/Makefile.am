AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../../include -I@srcdir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN) -Wno-unused-function -Wno-unused-variable

# Compile generated C files using C++ compiler
CC=$(CXX)
AM_CFLAGS = $(AM_CXXFLAGS)

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
	-$(AM_V_at)rmdir @srcdir@/generated
	-$(AM_V_at)rm -f @srcdir@/stamp-generated

@srcdir@/stamp-generated:
	$(AM_V_at)mkdir -p @srcdir@/generated
	$(AM_V_at)touch @srcdir@/stamp-generated

# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
@srcdir@/generated/CvcLexer.h: Cvc.g @srcdir@/stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	$(AM_V_GEN)$(ANTLR) -o "@srcdir@/generated" "@srcdir@/Cvc.g"

# These don't actually depend on CvcLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@srcdir@/generated/CvcLexer.c @srcdir@/generated/CvcParser.h @srcdir@/generated/CvcParser.c $(ANTLR_TOKEN_STUFF): @srcdir@/generated/CvcLexer.h
