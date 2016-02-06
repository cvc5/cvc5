AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN) $(WNO_PARENTHESES) $(WNO_TAUTOLOGICAL_COMPARE) -Wno-unused-function -Wno-unused-variable $(WNO_UNINITIALIZED) $(WNO_CONVERSION_NULL)

# Compile generated C files using C++ compiler
CC=$(CXX)
AM_CFLAGS = $(AM_CXXFLAGS)

ANTLR_OPTS =

# hide this included makefile from automake
@mk_include@ @srcdir@/../Makefile.antlr_tracing

noinst_LTLIBRARIES = libparsercvc.la

ANTLR_TOKEN_STUFF = \
	@builddir@/Cvc.tokens
ANTLR_LEXER_STUFF = \
	@builddir@/CvcLexer.h \
	@builddir@/CvcLexer.c \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@builddir@/CvcParser.h \
	@builddir@/CvcParser.c
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsercvc_la_SOURCES = \
	Cvc.g \
	cvc_input.h \
	cvc_input.cpp \
	$(ANTLR_STUFF)

BUILT_SOURCES = \
	@builddir@/Cvc.tokens \
	@builddir@/CvcLexer.h \
	@builddir@/CvcLexer.c \
	@builddir@/CvcParser.h \
	@builddir@/CvcParser.c \
	stamp-generated

EXTRA_DIST = \
	README \
	stamp-generated

DISTCLEANFILES = $(ANTLR_STUFF)
distclean-local:
	-$(AM_V_at)rmdir generated
	-$(AM_V_at)rm -f stamp-generated

stamp-generated:
	$(AM_V_at)mkdir -p generated
	$(AM_V_at)touch stamp-generated

# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
@builddir@/CvcLexer.h: Cvc.g stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	@if test -z "$(ANTLR)"; then echo "ERROR: antlr parser generator cannot be found, cannot generate the parser" >&2; exit 1; fi
	$(AM_V_GEN)$(ANTLR) $(ANTLR_OPTS) -fo "@builddir@" "@srcdir@/Cvc.g"

# These don't actually depend on CvcLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@builddir@/CvcLexer.c @builddir@/CvcParser.h @builddir@/CvcParser.c $(ANTLR_TOKEN_STUFF): @builddir@/CvcLexer.h
