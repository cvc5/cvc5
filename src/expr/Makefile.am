# if coverage is enabled:
# COVERAGE_ON = yes from configure.ac
# Using an inline conditional function to choose between absolute and
# relative paths for options files
# lcov does not support relative paths and src/options and src/expr
# in particular were breaking it
# Building with coverage will cause portability issues in some cases

VPATH = $(if $(COVERAGE_ON), $(realpath @srcdir@), @srcdir@)

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	$(if $(COVERAGE_ON), -I@abs_builddir@/.. -I@abs_srcdir@/../include -I@abs_srcdir@/.., \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libexpr.la

# For some reason statistics were in libutil. No idea why though.
libexpr_la_SOURCES = \
	array.h \
	array_store_all.cpp \
	array_store_all.h \
	ascription_type.h \
	attribute.h \
	attribute.cpp \
	attribute_internals.h \
	attribute_unique_id.h \
	chain.h \
	emptyset.cpp \
	emptyset.h \
	expr_iomanip.cpp \
	expr_iomanip.h \
	expr_manager_scope.h \
	expr_stream.h \
	kind_map.h \
	matcher.h \
	node.cpp \
	node.h \
	node_builder.h \
	node_manager.cpp \
	node_manager.h \
	node_manager_attributes.h \
	node_manager_listeners.cpp \
	node_manager_listeners.h \
	node_self_iterator.h \
	node_value.cpp \
	node_value.h \
	pickle_data.cpp \
	pickle_data.h \
	pickler.cpp \
	pickler.h \
	symbol_table.cpp \
	symbol_table.h \
	type.cpp \
	type.h \
	type_checker.h \
	type_node.cpp \
	type_node.h \
	variable_type_map.h \
	datatype.h \
	datatype.cpp \
	record.cpp \
	record.h \
	uninterpreted_constant.cpp \
	uninterpreted_constant.h

nodist_libexpr_la_SOURCES = \
	kind.h \
	kind.cpp \
	metakind.h \
	metakind.cpp \
	type_properties.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	type_checker.cpp

EXTRA_DIST = \
	array.i \
	chain.i \
	array_store_all.i \
	ascription_type.i \
	datatype.i \
	emptyset.i \
	kind_template.h \
	kind_template.cpp \
	metakind_template.h \
	metakind_template.cpp \
	type_properties_template.h \
	expr_manager_template.h \
	expr_manager_template.cpp \
	expr_template.h \
	expr_template.cpp \
	type_checker_template.cpp \
	mkkind \
	mkmetakind \
	mkexpr \
	expr_stream.i \
	expr_manager.i \
	symbol_table.i \
	type.i \
	kind.i \
	expr.i \
	record.i \
	variable_type_map.i \
	uninterpreted_constant.i

BUILT_SOURCES = \
	kind.h \
	kind.cpp \
	metakind.h \
	metakind.cpp \
	type_properties.h \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	type_checker.cpp \
	$(top_builddir)/src/expr/.subdirs

CLEANFILES = \
	kind.h \
	kind.cpp \
	metakind.h \
	metakind.cpp \
	expr.h \
	expr.cpp \
	expr_manager.h \
	expr_manager.cpp \
	type_checker.cpp \
	type_properties.h \
	$(top_builddir)/src/expr/.subdirs

$(top_builddir)/src/expr/.subdirs: $(top_srcdir)/src/Makefile.theories  @top_srcdir@/src/mksubdirs
	$(AM_V_at)test -d $(top_builddir)/src/expr || mkdir $(top_builddir)/src/expr
	$(AM_V_at)chmod +x @top_srcdir@/src/mksubdirs
	$(AM_V_at)( @top_srcdir@/src/mksubdirs $(if $(COVERAGE_ON), "$(abs_top_srcdir)", "$(top_srcdir)")) > $(top_builddir)/src/expr/.subdirs.tmp
	@if ! diff -q $(top_builddir)/src/expr/.subdirs $(top_builddir)/src/expr/.subdirs.tmp &>/dev/null; then \
		echo "  GEN   " $@; \
		$(am__mv) $(top_builddir)/src/expr/.subdirs.tmp $(top_builddir)/src/expr/.subdirs; \
	fi

kind.h: kind_template.h mkkind @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkkind \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

kind.cpp: kind_template.cpp mkkind @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkkind \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

metakind.h: metakind_template.h mkmetakind @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkmetakind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkmetakind \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

metakind.cpp: metakind_template.cpp mkmetakind @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkmetakind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkmetakind \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

type_properties.h: type_properties_template.h mkkind @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkkind
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkkind \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr.h: expr_template.h mkexpr @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr.cpp: expr_template.cpp mkexpr @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr_manager.h: expr_manager_template.h mkexpr @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

expr_manager.cpp: expr_manager_template.cpp mkexpr @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

type_checker.cpp: type_checker_template.cpp mkexpr @top_builddir@/src/expr/.subdirs $(if $(COVERAGE_ON), @abs_top_srcdir@, @top_srcdir@)/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkexpr
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkexpr \
		$< \
		`cat @top_builddir@/src/expr/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

.PHONY: builts
builts: $(BUILT_SOURCES)
