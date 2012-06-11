AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libquantifiers.la

libquantifiers_la_SOURCES = \
	theory_quantifiers_type_rules.h \
	theory_quantifiers.h \
	quantifiers_rewriter.h \
	quantifiers_rewriter.cpp \
	theory_quantifiers.cpp \
	theory_quantifiers_instantiator.h \
	theory_quantifiers_instantiator.cpp \
	instantiation_engine.h \
	instantiation_engine.cpp \
	model_engine.h \
	model_engine.cpp

EXTRA_DIST = kinds