AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libexpr.la

libexpr_la_SOURCES = \
	node.h \
	node.cpp \
	type_node.h \
	type_node.cpp \
	builtin_type_rules.h \
	node_builder.h \
	convenience_node_builders.h \
	@srcdir@/expr.h \
	type.h \
	type.cpp \
	node_value.h \
	node_manager.h \
	@srcdir@/expr_manager.h \
	attribute.h \
	attribute.cpp \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	node_manager.cpp \
	@srcdir@/expr_manager.cpp \
	node_value.cpp \
	@srcdir@/expr.cpp \
	command.h \
	command.cpp \
	declaration_scope.h \
	declaration_scope.cpp \
	expr_manager_scope.h 

EXTRA_DIST = \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	@srcdir@/expr_manager.h \
	@srcdir@/expr.h \
	@srcdir@/expr_manager.cpp \
	@srcdir@/expr.cpp \
	@srcdir@/type.h \
	@srcdir@/type.cpp \
	kind_template.h \
	metakind_template.h \
	expr_manager_template.h \
	expr_manager_template.cpp \
	expr_template.h \
	expr_template.cpp

include @top_srcdir@/src/theory/Makefile.subdirs

@srcdir@/kind.h: kind_template.h mkkind builtin_kinds @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkkind \
		$< \
		@srcdir@/builtin_kinds \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

@srcdir@/metakind.h: metakind_template.h mkmetakind builtin_kinds @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkmetakind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkmetakind \
		$< \
		@srcdir@/builtin_kinds \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

@srcdir@/expr.h: expr_template.h mkexpr builtin_kinds @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		@srcdir@/builtin_kinds \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

@srcdir@/expr.cpp: expr_template.cpp mkexpr builtin_kinds @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		@srcdir@/builtin_kinds \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

@srcdir@/expr_manager.h: expr_manager_template.h mkexpr builtin_kinds @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		@srcdir@/builtin_kinds \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

@srcdir@/expr_manager.cpp: expr_manager_template.cpp mkexpr builtin_kinds @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		@srcdir@/builtin_kinds \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

BUILT_SOURCES = \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	@srcdir@/expr.h \
	@srcdir@/expr.cpp \
	@srcdir@/expr_manager.h \
	@srcdir@/expr_manager.cpp

dist-hook: \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	@srcdir@/expr.h \
	@srcdir@/expr.cpp \
	@srcdir@/expr_manager.h \
	@srcdir@/expr_manager.cpp

MAINTAINERCLEANFILES = \
	@srcdir@/kind.h \
	@srcdir@/metakind.h \
	@srcdir@/expr.h \
	@srcdir@/expr.cpp \
	@srcdir@/expr_manager.h \
	@srcdir@/expr_manager.cpp
