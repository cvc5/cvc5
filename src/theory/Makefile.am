AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libtheory.la

libtheory_la_SOURCES = \
	@srcdir@/theoryof_table.h \
	theory_engine.h \
	theory_engine.cpp \
	theory.h \
	theory.cpp

libtheory_la_LIBADD = \
	@builddir@/booleans/libbooleans.la \
	@builddir@/uf/libuf.la \
	@builddir@/arith/libarith.la \
	@builddir@/arrays/libarrays.la \
	@builddir@/bv/libbv.la

EXTRA_DIST = \
	@srcdir@/theoryof_table.h \
	theoryof_table_template.h

include @top_srcdir@/src/theory/Makefile.subdirs

@srcdir@/theoryof_table.h: theoryof_table_template.h mktheoryof @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheoryof
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mktheoryof \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

BUILT_SOURCES = @srcdir@/theoryof_table.h
dist-hook: @srcdir@/theoryof_table.h
MAINTAINERCLEANFILES = @srcdir@/theoryof_table.h

SUBDIRS = booleans uf arith arrays bv
