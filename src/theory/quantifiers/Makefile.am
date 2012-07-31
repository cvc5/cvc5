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
	model_engine.cpp \
	inst_when_mode.cpp \
	inst_when_mode.h \
	literal_match_mode.cpp \
	literal_match_mode.h \
	relevant_domain.h \
	relevant_domain.cpp \
	rep_set_iterator.h \
	rep_set_iterator.cpp \
	term_database.h \
	term_database.cpp \
	first_order_model.h \
	first_order_model.cpp \
	model_builder.h \
	model_builder.cpp

EXTRA_DIST = \
	kinds \
	options_handlers.h
