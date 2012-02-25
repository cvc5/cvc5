AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = builtin booleans uf arith arrays bv datatypes
DIST_SUBDIRS = $(SUBDIRS) example

noinst_LTLIBRARIES = libtheory.la

libtheory_la_SOURCES = \
	output_channel.h \
	interrupted.h \
	theory_engine.h \
	theory_engine.cpp \
	theory_test_utils.h \
	theory.h \
	theory.cpp \
	theory_registrar.h \
	rewriter.h \
	rewriter_attributes.h \
	rewriter.cpp \
	substitutions.h \
	substitutions.cpp \
	valuation.h \
	valuation.cpp \
	shared_terms_database.h \
	shared_terms_database.cpp \
	term_registration_visitor.h \
	term_registration_visitor.cpp

nodist_libtheory_la_SOURCES = \
	rewriter_tables.h \
	theory_traits.h

libtheory_la_LIBADD = \
	@builddir@/builtin/libbuiltin.la \
	@builddir@/booleans/libbooleans.la \
	@builddir@/uf/libuf.la \
	@builddir@/arith/libarith.la \
	@builddir@/arrays/libarrays.la \
	@builddir@/bv/libbv.la \
	@builddir@/datatypes/libdatatypes.la

EXTRA_DIST = \
	rewriter_tables_template.h \
	theory_traits_template.h \
	mktheorytraits \
	mkrewriter \
	Makefile.subdirs

BUILT_SOURCES = \
	rewriter_tables.h \
	theory_traits.h

CLEANFILES = \
	rewriter_tables.h \
	theory_traits.h

include @top_srcdir@/src/theory/Makefile.subdirs

rewriter_tables.h: rewriter_tables_template.h mkrewriter @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkrewriter
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkrewriter \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

theory_traits.h: theory_traits_template.h mktheorytraits @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mktheorytraits \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

AM_V_CHECK = $(am__v_CHECK_$(V))
am__v_CHECK_ = $(am__v_CHECK_$(AM_DEFAULT_VERBOSITY))
am__v_CHECK_0 = @echo "  CHECK " $@;

.PHONY: theory-properties
theory-properties:
	$(AM_V_CHECK)@srcdir@/mktheorytraits \
		theory_traits_template.h \
		`cat @top_builddir@/src/theory/.subdirs` \
	> /dev/null
all-local check-local: theory-properties
