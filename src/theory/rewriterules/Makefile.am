AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
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
	theory_rewriterules_params.h

EXTRA_DIST = \
	kinds
