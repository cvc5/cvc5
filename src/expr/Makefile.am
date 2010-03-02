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
	@srcdir@/kind.h \
	node_builder.cpp \
	node_manager.cpp \
	expr_manager.cpp \
	node_value.cpp \
	expr.cpp \
	type.cpp \
	command.h \
	command.cpp

EXTRA_DIST = \
	@srcdir@/kind.h \
	kind_prologue.h \
	kind_middle.h \
	kind_epilogue.h

@srcdir@/kind.h: mkkind kind_prologue.h kind_middle.h kind_epilogue.h builtin_kinds @top_srcdir@/src/theory/Makefile.in @top_srcdir@/src/theory/*/kinds
	chmod +x @srcdir@/mkkind
	(@srcdir@/mkkind \
		@srcdir@/kind_prologue.h \
		@srcdir@/kind_middle.h \
		@srcdir@/kind_epilogue.h \
		@srcdir@/builtin_kinds \
		`grep '^SUBDIRS = ' @top_srcdir@/src/theory/Makefile.in | cut -d' ' -f3- | tr ' ' "\n" | xargs -i__D__ echo @top_srcdir@/src/theory/__D__/kinds` \
	> @srcdir@/kind.h) || (rm -f @srcdir@/kind.h && exit 1)

BUILT_SOURCES = @srcdir@/kind.h
dist-hook: @srcdir@/kind.h
MAINTAINERCLEANFILES = @srcdir@/kind.h
