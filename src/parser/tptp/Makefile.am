AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN) -Wno-unused-function -Wno-unused-variable

# Compile generated C files using C++ compiler
AM_CFLAGS = $(AM_CXXFLAGS)
CC=$(CXX)

ANTLR_OPTS =

# hide this included makefile from automake
@mk_include@ @srcdir@/../Makefile.antlr_tracing

noinst_LTLIBRARIES = libparsertptp.la

ANTLR_TOKEN_STUFF = \
	@srcdir@/generated/Tptp.tokens
ANTLR_LEXER_STUFF = \
	@srcdir@/generated/TptpLexer.h \
	@srcdir@/generated/TptpLexer.c \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@srcdir@/generated/TptpParser.h \
	@srcdir@/generated/TptpParser.c
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsertptp_la_SOURCES = \
	Tptp.g \
	tptp.h \
	tptp.cpp \
	tptp_input.h \
	tptp_input.cpp \
	$(ANTLR_STUFF)

BUILT_SOURCES = $(ANTLR_STUFF) @srcdir@/stamp-generated

EXTRA_DIST = @srcdir@/stamp-generated

MAINTAINERCLEANFILES = $(ANTLR_STUFF)
maintainer-clean-local:
	-$(AM_V_at)rmdir @srcdir@/generated
	-$(AM_V_at)rm -f @srcdir@/stamp-generated

@srcdir@/stamp-generated:
	$(AM_V_at)mkdir -p @srcdir@/generated
	$(AM_V_at)touch @srcdir@/stamp-generated

# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
@srcdir@/generated/TptpLexer.h: Tptp.g @srcdir@/stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	@if test -z "$(ANTLR)"; then echo "ERROR: antlr parser generator cannot be found, cannot generate the parser" >&2; exit 1; fi
	$(AM_V_GEN)$(ANTLR) $(ANTLR_OPTS) -fo "@srcdir@/generated" "@srcdir@/Tptp.g"

# These don't actually depend on TptpLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@srcdir@/generated/TptpLexer.c @srcdir@/generated/TptpParser.h @srcdir@/generated/TptpParser.c $(ANTLR_TOKEN_STUFF): @srcdir@/generated/TptpLexer.h
