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

noinst_LTLIBRARIES = libparsersmt1.la

ANTLR_TOKEN_STUFF = \
	@builddir@/Smt1.tokens
ANTLR_LEXER_STUFF = \
	@builddir@/Smt1Lexer.h \
	@builddir@/Smt1Lexer.c \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@builddir@/Smt1Parser.h \
	@builddir@/Smt1Parser.c
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsersmt1_la_SOURCES = \
	Smt1.g \
        smt1.h \
        smt1.cpp \
	smt1_input.h \
	smt1_input.cpp \
	$(ANTLR_STUFF)

BUILT_SOURCES = \
	@builddir@/Smt1.tokens \
	@builddir@/Smt1Lexer.h \
	@builddir@/Smt1Lexer.c \
	@builddir@/Smt1Parser.h \
	@builddir@/Smt1Parser.c \
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
@builddir@/Smt1Lexer.h: Smt1.g stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	@if test -z "$(ANTLR)"; then echo "ERROR: antlr parser generator cannot be found, cannot generate the parser" >&2; exit 1; fi
	$(AM_V_GEN)$(ANTLR) $(ANTLR_OPTS) -fo "@builddir@" "@srcdir@/Smt1.g"

# These don't actually depend on Smt1Lexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@builddir@/Smt1Lexer.c @builddir@/Smt1Parser.h @builddir@/Smt1Parser.c $(ANTLR_TOKEN_STUFF): @builddir@/Smt1Lexer.h
