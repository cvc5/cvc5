AM_CPPFLAGS = \
	-D__BUILDING_CVC4PARSERLIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN) -Wno-unused-function -Wno-unused-variable $(WNO_CONVERSION_NULL)

# Compile generated C files using C++ compiler
CC=$(CXX)
AM_CFLAGS = $(AM_CXXFLAGS)

ANTLR_OPTS =

# hide this included makefile from automake
@mk_include@ @srcdir@/../Makefile.antlr_tracing

noinst_LTLIBRARIES = libparsercvc.la

ANTLR_TOKEN_STUFF = \
	@abs_builddir@/generated/Cvc.tokens
ANTLR_LEXER_STUFF = \
	@abs_builddir@/generated/CvcLexer.h \
	@abs_builddir@/generated/CvcLexer.c \
	$(ANTLR_TOKEN_STUFF)
ANTLR_PARSER_STUFF = \
	@abs_builddir@/generated/CvcParser.h \
	@abs_builddir@/generated/CvcParser.c
ANTLR_STUFF = \
	$(ANTLR_LEXER_STUFF) \
	$(ANTLR_PARSER_STUFF)

libparsercvc_la_SOURCES = \
	Cvc.g \
	cvc_input.h \
	cvc_input.cpp \
	$(ANTLR_STUFF)

BUILT_SOURCES = $(ANTLR_STUFF) stamp-generated

EXTRA_DIST = README

DISTCLEANFILES = $(ANTLR_STUFF)
distclean-local:
	-$(AM_V_at)rmdir generated
	-$(AM_V_at)rm -f stamp-generated

stamp-generated:
	$(AM_V_at)mkdir -p generated
	$(AM_V_at)touch stamp-generated

# antlr doesn't overwrite output files, it just leaves them.  So we have to delete them first.
@abs_builddir@/generated/CvcLexer.h: Cvc.g stamp-generated
	-$(AM_V_at)rm -f $(ANTLR_STUFF)
	@if test -z "$(ANTLR)"; then echo "ERROR: antlr parser generator cannot be found, cannot generate the parser" >&2; exit 1; fi
	$(AM_V_GEN)$(ANTLR) $(ANTLR_OPTS) -fo "generated" "@srcdir@/Cvc.g"

# These don't actually depend on CvcLexer.h, but if we're doing parallel
# make and the lexer needs to be rebuilt, we have to keep the rules
# from running in parallel (since the token files will be deleted &
# recreated)
@abs_builddir@/generated/CvcLexer.c @abs_builddir@/generated/CvcParser.h @abs_builddir@/generated/CvcParser.c $(ANTLR_TOKEN_STUFF): @abs_builddir@/generated/CvcLexer.h
