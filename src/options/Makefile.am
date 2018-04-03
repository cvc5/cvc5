# if coverage is enabled:
# COVERAGE_ON = yes from configure.ac
# Using an inline conditional function to choose between absolute and
# relative paths for options files
# lcov does not support relative paths and src/options and src/expr
# in particular were breaking it
# Building with coverage will cause portability issues in some cases

VPATH = $(if $(COVERAGE_ON), $(realpath @srcdir@), @srcdir@)

OPTIONS_CONFIG_FILES = \
	arith_options.toml \
	arrays_options.toml \
	base_options.toml \
	booleans_options.toml \
	builtin_options.toml \
	bv_options.toml \
	datatypes_options.toml \
	decision_options.toml \
	expr_options.toml \
	fp_options.toml \
	idl_options.toml \
	main_options.toml \
	parser_options.toml \
	printer_options.toml \
	proof_options.toml \
	prop_options.toml \
	quantifiers_options.toml \
	sep_options.toml \
	sets_options.toml \
	smt_options.toml \
	strings_options.toml \
	theory_options.toml \
	uf_options.toml

OPTIONS_GEN_H = $(OPTIONS_CONFIG_FILES:.toml=.h)

OPTIONS_GEN_CPP = $(OPTIONS_CONFIG_FILES:.toml=.cpp)

CPP_TEMPLATE_FILES = \
	module_template.h \
	module_template.cpp \
	options_holder_template.h \
	options_template.cpp

DOCUMENTATION_FILES = \
	../../doc/cvc4.1 \
	../../doc/SmtEngine.3cvc \
	../../doc/options.3cvc

DOCUMENTATION_TEMPLATE_FILES = \
	../../doc/cvc4.1_template \
	../../doc/SmtEngine.3cvc_template \
	../../doc/options.3cvc_template


AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	$(if $(COVERAGE_ON), -I@abs_builddir@/.. -I@abs_srcdir@/../include -I@abs_srcdir@/.., \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..)
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = liboptions.la

liboptions_la_SOURCES = \
	arith_heuristic_pivot_rule.cpp \
	arith_heuristic_pivot_rule.h \
	arith_propagation_mode.cpp \
	arith_propagation_mode.h \
	arith_unate_lemma_mode.cpp \
	arith_unate_lemma_mode.h \
	argument_extender_implementation.cpp \
	argument_extender_implementation.h \
	argument_extender.h \
	base_handlers.h \
	bv_bitblast_mode.cpp \
	bv_bitblast_mode.h \
	datatypes_modes.h \
	decision_mode.cpp \
	decision_mode.h \
	decision_weight.h \
	didyoumean.cpp \
	didyoumean.h \
	language.cpp \
	language.h \
	open_ostream.cpp \
	open_ostream.h \
	option_exception.h \
	options.h \
	options_handler.cpp \
	options_handler.h \
	options_public_functions.cpp \
	printer_modes.cpp \
	printer_modes.h \
	quantifiers_modes.cpp \
	quantifiers_modes.h \
	set_language.cpp \
	set_language.h \
	simplification_mode.cpp \
	simplification_mode.h \
	sygus_out_mode.h \
	theoryof_mode.cpp \
	theoryof_mode.h \
	ufss_mode.h


nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	$(OPTIONS_GEN_H) \
	$(OPTIONS_GEN_CPP)


BUILT_SOURCES = \
	options.cpp


CLEANFILES = \
	$(BUILT_SOURCES) \
	$(OPTIONS_GEN_H) \
	$(OPTIONS_GEN_CPP) \
	$(DOCUMENTATION_FILES) \
	options_holder.h


EXTRA_DIST = \
	options.cpp \
	options_holder.h \
	$(OPTIONS_GEN_CPP) \
	$(OPTIONS_GEN_H) \
	$(OPTIONS_CONFIG_FILES) \
	$(CPP_TEMPLATE_FILES) \
	$(DOCUMENTATION_FILES) \
	mkoptions.py \
	language.i \
	option_exception.i \
	options.i



# Make sure the implicit rules never mistake a _template.cpp or _template.h
# file for source file.
$(CPP_TEMPLATE_FILES):;

# All source/doc files are generated in one pass with rule options.cpp. Note
# that this is done incrementally since mkoptions.py checks if a generated file
# changed before writing to the file. No global re-compilation of all generated
# files happens if only individual files were modified.
$(OPTIONS_GEN_CPP) $(OPTIONS_GEN_H) options_holder.h $(DOCUMENTATION_FILES): options.cpp

options.cpp: mkoptions.py $(CPP_TEMPLATE_FILES) $(OPTIONS_CONFIG_FILES) $(DOCUMENTATION_TEMPLATE_FILES)
	@srcdir@/mkoptions.py @abs_srcdir@ ../../doc . $(addprefix @abs_srcdir@/, $(OPTIONS_CONFIG_FILES))

# This rule is ugly.  It's needed to ensure that automake's dependence
# includes are available during distclean, even though they come from
# directories that are cleaned first.  Without this rule, "distclean"
# fails.
%.Plo:; $(MKDIR_P) "$(dir $@)" && : > "$@"
