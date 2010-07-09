AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libexpr.la

libexpr_la_SOURCES = \
	node.h \
	node.cpp \
	type_node.h \
	type_node.cpp \
	type_constant.h \
	node_builder.h \
	convenience_node_builders.h \
	type.h \
	type.cpp \
	node_value.h \
	node_manager.h \
	attribute.h \
	attribute_internals.h \
	attribute.cpp \
	node_manager.cpp \
	node_value.cpp \
	command.h \
	command.cpp \
	declaration_scope.h \
	declaration_scope.cpp \
	expr_manager_scope.h 
nodist_libexpr_la_SOURCES = \
	kind.h \
	metakind.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp

EXTRA_DIST = \
	kind_template.h \
	metakind_template.h \
	expr_manager_template.h \
	expr_manager_template.cpp \
	expr_template.h \
	expr_template.cpp \
	mkkind \
	mkmetakind \
	mkexpr

BUILT_SOURCES = \
	kind.h \
	metakind.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	$(top_builddir)/src/theory/.subdirs

CLEANFILES = \
	kind.h \
	metakind.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	$(top_builddir)/src/theory/.subdirs

include @top_srcdir@/src/theory/Makefile.subdirs

kind.h: kind_template.h mkkind @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkkind \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

metakind.h: metakind_template.h mkmetakind @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkmetakind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkmetakind \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr.h: expr_template.h mkexpr @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr.cpp: expr_template.cpp mkexpr @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr_manager.h: expr_manager_template.h mkexpr @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr_manager.cpp: expr_manager_template.cpp mkexpr @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)
