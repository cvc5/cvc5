AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libexpr.la

libexpr_la_SOURCES = \
	node.h \
	node.cpp \
	type_node.h \
	type_node.cpp \
	node_builder.h \
	convenience_node_builders.h \
	type.h \
	type.cpp \
	node_value.h \
	node_value.cpp \
	node_manager.h \
	node_manager.cpp \
	node_manager_attributes.h \
	type_checker.h \
	attribute_unique_id.h \
	attribute.h \
	attribute_internals.h \
	attribute.cpp \
	command.h \
	command.cpp \
	symbol_table.h \
	symbol_table.cpp \
	expr_manager_scope.h \
	node_self_iterator.h \
	variable_type_map.h \
	pickle_data.h \
	pickle_data.cpp \
	pickler.h \
	pickler.cpp \
	node_self_iterator.h \
	expr_stream.h \
	kind_map.h

nodist_libexpr_la_SOURCES = \
	kind.h \
	metakind.h \
	type_properties.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	type_checker.cpp

EXTRA_DIST = \
	kind_template.h \
	metakind_template.h \
	type_properties_template.h \
	expr_manager_template.h \
	expr_manager_template.cpp \
	expr_template.h \
	expr_template.cpp \
	type_checker_template.cpp \
	options_handlers.h \
	mkkind \
	mkmetakind \
	mkexpr \
	expr_stream.i \
	expr_manager.i \
	symbol_table.i \
	command.i \
	type.i \
	kind.i \
	expr.i \
	variable_type_map.i

BUILT_SOURCES = \
	kind.h \
	metakind.h \
	type_properties.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	type_checker.cpp \
	$(top_builddir)/src/theory/.subdirs

CLEANFILES = \
	kind.h \
	metakind.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	type_checker.cpp \
	type_properties.h \
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

type_properties.h: type_properties_template.h mkkind @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkkind \
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

type_checker.cpp: type_checker_template.cpp mkexpr @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

.PHONY: builts
builts: $(BUILT_SOURCES)
