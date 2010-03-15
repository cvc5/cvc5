AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden

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
	theoryof_table_prologue.h \
	theoryof_table_middle.h \
	theoryof_table_epilogue.h

@srcdir@/theoryof_table.h: @srcdir@/mktheoryof theoryof_table_prologue.h theoryof_table_middle.h theoryof_table_epilogue.h @top_srcdir@/src/theory/Makefile.in @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheoryof
	$(AM_V_GEN)(@srcdir@/mktheoryof \
		@srcdir@/theoryof_table_prologue.h \
		@srcdir@/theoryof_table_middle.h \
		@srcdir@/theoryof_table_epilogue.h \
		`grep '^SUBDIRS = ' @top_srcdir@/src/theory/Makefile.in | cut -d' ' -f3- | tr ' ' "\n" | xargs -i__D__ echo @top_srcdir@/src/theory/__D__/kinds` \
	> @srcdir@/theoryof_table.h) || (rm -f @srcdir@/theoryof_table.h && exit 1)

BUILT_SOURCES = @srcdir@/theoryof_table.h
dist-hook: @srcdir@/theoryof_table.h
MAINTAINERCLEANFILES = @srcdir@/theoryof_table.h

SUBDIRS = booleans uf arith arrays bv
