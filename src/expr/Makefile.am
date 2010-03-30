AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden

noinst_LTLIBRARIES = libexpr.la

libexpr_la_SOURCES = \
	node.h \
	node.cpp \
	node_builder.h \
	expr.h \
	type.h \
	node_value.h \
	node_manager.h \
	expr_manager.h \
	attribute.h \
	attribute.cpp \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	node_manager.cpp \
	expr_manager.cpp \
	node_value.cpp \
	expr.cpp \
	type.cpp \
	command.h \
	command.cpp

EXTRA_DIST = \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	kind_template.h \
	metakind_template.h

@srcdir@/kind.h: mkkind kind_template.h builtin_kinds @top_srcdir@/src/theory/Makefile.in @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_GEN)(@srcdir@/mkkind \
		@srcdir@/kind_template.h \
		@srcdir@/builtin_kinds \
		`grep '^SUBDIRS = ' @top_srcdir@/src/theory/Makefile.in | cut -d' ' -f3- | tr ' ' "\n" | xargs -i__D__ echo @top_srcdir@/src/theory/__D__/kinds` \
	> @srcdir@/kind.h) || (rm -f @srcdir@/kind.h && exit 1)

@srcdir@/metakind.h: mkmetakind metakind_template.h builtin_kinds @top_srcdir@/src/theory/Makefile.in @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkmetakind
	$(AM_V_GEN)(@srcdir@/mkmetakind \
		@srcdir@/metakind_template.h \
		@srcdir@/builtin_kinds \
		`grep '^SUBDIRS = ' @top_srcdir@/src/theory/Makefile.in | cut -d' ' -f3- | tr ' ' "\n" | xargs -i__D__ echo @top_srcdir@/src/theory/__D__/kinds` \
	> @srcdir@/metakind.h) || (rm -f @srcdir@/metakind.h && exit 1)

BUILT_SOURCES = @srcdir@/kind.h @srcdir@/metakind.h
dist-hook: @srcdir@/kind.h @srcdir@/metakind.h
MAINTAINERCLEANFILES = @srcdir@/kind.h @srcdir@/metakind.h
