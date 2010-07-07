AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

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
	shared_data.cpp
nodist_libtheory_la_SOURCES = \
	theoryof_table.h

libtheory_la_LIBADD = \
	@builddir@/builtin/libbuiltin.la \
	@builddir@/booleans/libbooleans.la \
	@builddir@/uf/libuf.la \
	@builddir@/arith/libarith.la \
	@builddir@/arrays/libarrays.la \
	@builddir@/bv/libbv.la

EXTRA_DIST = \
	theoryof_table_template.h \
	mktheoryof \
	Makefile.subdirs

BUILT_SOURCES = \
	theoryof_table.h

CLEANFILES = \
	theoryof_table.h

include @top_srcdir@/src/theory/Makefile.subdirs

theoryof_table.h: theoryof_table_template.h mktheoryof @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheoryof
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mktheoryof \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

SUBDIRS = builtin booleans uf arith arrays bv
