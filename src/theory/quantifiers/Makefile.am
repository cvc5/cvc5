AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libquantifiers.la

libquantifiers_la_SOURCES = \
	theory_quantifiers_type_rules.h \
	theory_quantifiers.h \
	quantifiers_rewriter.h \
	quantifiers_rewriter.cpp \
	theory_quantifiers.cpp \
	instantiation_engine.h \
	instantiation_engine.cpp \
	trigger.h \
	trigger.cpp \
	candidate_generator.h \
	candidate_generator.cpp \
	inst_match.h \
	inst_match.cpp \
	model_engine.h \
	model_engine.cpp \
	modes.cpp \
	modes.h \
	relevant_domain.h \
	relevant_domain.cpp \
	term_database.h \
	term_database.cpp \
	first_order_model.h \
	first_order_model.cpp \
	model_builder.h \
	model_builder.cpp \
	quantifiers_attributes.h \
	quantifiers_attributes.cpp \
	inst_gen.h \
	inst_gen.cpp \
	quant_util.h \
	quant_util.cpp \
	inst_match_generator.h \
	inst_match_generator.cpp \
	macros.h \
	macros.cpp \
	inst_strategy_e_matching.h \
	inst_strategy_e_matching.cpp \
	inst_strategy_cbqi.h \
	inst_strategy_cbqi.cpp

EXTRA_DIST = \
	kinds \
	options_handlers.h
