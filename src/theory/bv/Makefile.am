AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbv.la

libbv_la_SOURCES = \
	theory_bv_utils.h \
	type_enumerator.h \
	bitblaster.h \
	bitblaster.cpp \
	bv_subtheory.h \
	bv_subtheory_core.h \
	bv_subtheory_core.cpp \
	bv_subtheory_bitblast.h \
	bv_subtheory_bitblast.cpp \
	bv_subtheory_inequality.h \
	bv_subtheory_inequality.cpp \
	bv_inequality_graph.h \
	bv_inequality_graph.cpp \
	bitblast_strategies.h \
	bitblast_strategies.cpp \
	slicer.h \
	slicer.cpp \
	theory_bv.h \
	theory_bv.cpp \
	theory_bv_rewrite_rules.h \
	theory_bv_rewrite_rules_core.h \
	theory_bv_rewrite_rules_operator_elimination.h \
	theory_bv_rewrite_rules_constant_evaluation.h \
	theory_bv_rewrite_rules_normalization.h \
	theory_bv_rewrite_rules_simplification.h \
	theory_bv_type_rules.h \
	theory_bv_rewriter.h \
	theory_bv_rewriter.cpp \
	cd_set_collection.h 

EXTRA_DIST = \
	kinds
