AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN) $(WNO_PARENTHESES) $(WNO_TAUTOLOGICAL_COMPARE) -Wno-unused-function -Wno-unused-variable

# Compile generated C files using C++ compiler
AM_CFLAGS = $(AM_CXXFLAGS)
CC=$(CXX)

ANTLR_OPTS =

# hide this included makefile from automake
@mk_include@ @srcdir@/../Makefile.antlr_tracing

noinst_LTLIBRARIES = libparsertptp.la

ANTLR_TOKEN_STUFF = \
	@builddir@/Tptp.tokens
ANTLR_LEXER_STUFF = \
	@builddir@/TptpLexer.h \
	@builddir@/TptpLexer.c \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@builddir@/TptpParser.h \
	@builddir@/TptpParser.c
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

BUILT_SOURCES = \
	@builddir@/Tptp.tokens \
	@builddir@/TptpLexer.h \
	@builddir@/TptpLexer.c \
	@builddir@/TptpParser.h \
	@builddir@/TptpParser.c \
	stamp-generated

EXTRA_DIST = \
	stamp-generated

DISTCLEANFILES = $(ANTLR_STUFF)
distclean-local:
	-$(AM_V_at)rmdir generated
	-$(AM_V_at)rm -f stamp-generated

stamp-generated:
	$(AM_V_at)mkdir -p generated
	$(AM_V_at)touch stamp-generated

# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
@builddir@/TptpLexer.h: Tptp.g stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	@if test -z "$(ANTLR)"; then echo "ERROR: antlr parser generator cannot be found, cannot generate the parser" >&2; exit 1; fi
	$(AM_V_GEN)$(ANTLR) $(ANTLR_OPTS) -fo "@builddir@" "@srcdir@/Tptp.g"

# These don't actually depend on TptpLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@builddir@/TptpLexer.c @builddir@/TptpParser.h @builddir@/TptpParser.c $(ANTLR_TOKEN_STUFF): @builddir@/TptpLexer.h
