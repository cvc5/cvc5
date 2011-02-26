AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = builtin booleans uf arith arrays bv

noinst_LTLIBRARIES = libtheory.la

libtheory_la_SOURCES = \
	output_channel.h \
	interrupted.h \
	theory_engine.h \
	theory_engine.cpp \
	theory_test_utils.h \
	theory.h \
	theory.cpp \
	shared_term_manager.h \
	shared_term_manager.cpp \
	shared_data.h \
	shared_data.cpp \
	rewriter.h \
	rewriter_attributes.h \
	rewriter.cpp \
	valuation.h \
	valuation.cpp

nodist_libtheory_la_SOURCES = \
	rewriter_tables.h \
	theory_traits.h

libtheory_la_LIBADD = \
	@builddir@/builtin/libbuiltin.la \
	@builddir@/booleans/libbooleans.la \
	@builddir@/uf/libuf.la \
	@builddir@/arith/libarith.la \
	@builddir@/arrays/libarrays.la \
	@builddir@/bv/libbv.la

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
	$(AM_V_GEN)(@srcdir@//mktheorytraits \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)
