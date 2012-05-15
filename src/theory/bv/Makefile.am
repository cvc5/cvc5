AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbv.la

libbv_la_SOURCES = \
	theory_bv_utils.h \
	bitblaster.h \
	bitblaster.cpp \
	bitblast_strategies.h \
	bitblast_strategies.cpp \
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

EXTRA_DIST = kinds
