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

noinst_LTLIBRARIES = libparsersmt2.la

ANTLR_TOKEN_STUFF = \
	@builddir@/Smt2.tokens
ANTLR_LEXER_STUFF = \
	@builddir@/Smt2Lexer.h \
	@builddir@/Smt2Lexer.c \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@builddir@/Smt2Parser.h \
	@builddir@/Smt2Parser.c
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsersmt2_la_SOURCES = \
	Smt2.g \
	smt2.h \
	smt2.cpp \
	smt2_input.h \
	smt2_input.cpp \
	sygus_input.h \
	sygus_input.cpp \
	$(ANTLR_STUFF)

BUILT_SOURCES = \
	@builddir@/Smt2.tokens \
	@builddir@/Smt2Lexer.h \
	@builddir@/Smt2Lexer.c \
	@builddir@/Smt2Parser.h \
	@builddir@/Smt2Parser.c \
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
@builddir@/Smt2Lexer.h: Smt2.g stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	@if test -z "$(ANTLR)"; then echo "ERROR: antlr parser generator cannot be found, cannot generate the parser" >&2; exit 1; fi
	$(AM_V_GEN)$(ANTLR) $(ANTLR_OPTS) -fo "@builddir@" "@srcdir@/Smt2.g"

# These don't actually depend on SmtLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@builddir@/Smt2Lexer.c @builddir@/Smt2Parser.h @builddir@/Smt2Parser.c $(ANTLR_TOKEN_STUFF): @builddir@/Smt2Lexer.h
