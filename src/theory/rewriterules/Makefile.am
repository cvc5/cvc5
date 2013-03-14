AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = librewriterules.la

librewriterules_la_SOURCES = \
	theory_rewriterules_rules.h \
	theory_rewriterules_rules.cpp \
	theory_rewriterules.h \
	theory_rewriterules.cpp \
	theory_rewriterules_rewriter.h \
	theory_rewriterules_type_rules.h \
	theory_rewriterules_preprocess.h \
	theory_rewriterules_params.h \
	rr_inst_match.h \
	rr_inst_match_impl.h \
	rr_inst_match.cpp \
	rr_trigger.h \
	rr_trigger.cpp \
	rr_candidate_generator.h \
	rr_candidate_generator.cpp \
	efficient_e_matching.h \
	efficient_e_matching.cpp

EXTRA_DIST = \
	kinds
