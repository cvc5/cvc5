AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

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

@srcdir@/theoryof_table.h: theoryof_table_template.h mktheoryof @top_srcdir@/src/theory/Makefile.in @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheoryof
	$(AM_V_at)mv -f $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mktheoryof \
		$< \
		`grep '^SUBDIRS = ' @top_srcdir@/src/theory/Makefile.in | cut -d' ' -f3- | tr ' ' "\n" | xargs -i__D__ echo @top_srcdir@/src/theory/__D__/kinds` \
	> $@) || (rm -f $@ && exit 1)

BUILT_SOURCES = @srcdir@/theoryof_table.h
dist-hook: @srcdir@/theoryof_table.h
MAINTAINERCLEANFILES = @srcdir@/theoryof_table.h

SUBDIRS = booleans uf arith arrays bv
