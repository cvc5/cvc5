AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = builtin booleans uf arith arrays bv datatypes quantifiers rewriterules
DIST_SUBDIRS = $(SUBDIRS) example

noinst_LTLIBRARIES = libtheory.la

libtheory_la_SOURCES = \
	logic_info.h \
	logic_info.cpp \
	output_channel.h \
	interrupted.h \
	type_enumerator.h \
	theory_engine.h \
	theory_engine.cpp \
	theory_test_utils.h \
	theory.h \
	theory.cpp \
	theoryof_mode.h \
	theory_registrar.h \
	rewriter.h \
	rewriter_attributes.h \
	rewriter.cpp \
	substitutions.h \
	substitutions.cpp \
	valuation.h \
	valuation.cpp \
	shared_terms_database.h \
	shared_terms_database.cpp \
	term_registration_visitor.h \
	term_registration_visitor.cpp \
	ite_simplifier.h \
	ite_simplifier.cpp \
	unconstrained_simplifier.h \
	unconstrained_simplifier.cpp \
	quantifiers_engine.h \
	quantifiers_engine.cpp \
	instantiator_default.h \
	instantiator_default.cpp \
	rr_inst_match.h \
	rr_inst_match_impl.h \
	rr_inst_match.cpp \
	rr_trigger.h \
	rr_trigger.cpp \
	rr_candidate_generator.h \
	rr_candidate_generator.cpp \
	inst_match.h \
	inst_match.cpp \
	trigger.h \
	trigger.cpp \
	model.h \
	model.cpp \
	candidate_generator.h \
	candidate_generator.cpp

nodist_libtheory_la_SOURCES = \
	rewriter_tables.h \
	instantiator_tables.cpp \
	theory_traits.h \
	type_enumerator.cpp

libtheory_la_LIBADD = \
	@builddir@/builtin/libbuiltin.la \
	@builddir@/booleans/libbooleans.la \
	@builddir@/uf/libuf.la \
	@builddir@/arith/libarith.la \
	@builddir@/arrays/libarrays.la \
	@builddir@/bv/libbv.la \
	@builddir@/datatypes/libdatatypes.la \
	@builddir@/quantifiers/libquantifiers.la \
	@builddir@/rewriterules/librewriterules.la

EXTRA_DIST = \
	rewriter_tables_template.h \
	instantiator_tables_template.cpp \
	theory_traits_template.h \
	type_enumerator_template.cpp \
	mktheorytraits \
	mkrewriter \
	mkinstantiator \
	Makefile.subdirs

BUILT_SOURCES = \
	rewriter_tables.h \
	instantiator_tables.cpp \
	theory_traits.h \
	type_enumerator.cpp

CLEANFILES = \
	rewriter_tables.h \
	instantiator_tables.cpp \
	theory_traits.h \
	type_enumerator.cpp

include @top_srcdir@/src/theory/Makefile.subdirs

rewriter_tables.h: rewriter_tables_template.h mkrewriter @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkrewriter
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkrewriter \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

instantiator_tables.cpp: instantiator_tables_template.cpp mkinstantiator @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mkinstantiator
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mkinstantiator \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

theory_traits.h: theory_traits_template.h mktheorytraits @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mktheorytraits \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

type_enumerator.cpp: type_enumerator_template.cpp mktheorytraits @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/mktheorytraits \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)
