# How options are built:
# Step 1: Copy the X_options source file into builddir as X_options.tmp.
#    X_options.tmp is a .PHONY rule to force this step to always be done.
# Step 2: Compare X_options.tmp to X_options.options.
#   If they are different, overwrite "X_options.options".
#   This is the file that we use to generate options from.
#   This is always up to dat with X_options. The change in name is just
#   to keep Makefile stage more explicit.
# Step 3: Generate X_options.sed from X_options.options using mkoptions.
# Step 4: Generate X_options.h from X_options.sed
# Step 5: Generate X_options.cpp from X_options.sed.
#   This stage also waits for X_options.h as otherwise it cannot compile.
#

OPTIONS_SRC_FILES = \
	arith_options \
	arrays_options \
	base_options \
	booleans_options \
	builtin_options \
	bv_options \
	datatypes_options \
	decision_options \
	expr_options \
	fp_options \
	idl_options \
	main_options \
	parser_options \
	printer_options \
	proof_options \
	prop_options \
	quantifiers_options \
	sep_options \
	sets_options \
	smt_options \
	strings_options \
	theory_options \
	uf_options

OPTIONS_TEMPS = \
	arith_options.tmp \
	arrays_options.tmp \
	base_options.tmp \
	booleans_options.tmp \
	builtin_options.tmp \
	bv_options.tmp \
	datatypes_options.tmp \
	decision_options.tmp \
	expr_options.tmp \
	fp_options.tmp \
	idl_options.tmp \
	main_options.tmp \
	parser_options.tmp \
	printer_options.tmp \
	proof_options.tmp \
	prop_options.tmp \
	quantifiers_options.tmp \
	sep_options.tmp \
	sets_options.tmp \
	smt_options.tmp \
	strings_options.tmp \
	theory_options.tmp \
	uf_options.tmp

OPTIONS_OPTIONS_FILES = \
	arith_options.options \
	arrays_options.options \
	base_options.options \
	booleans_options.options \
	builtin_options.options \
	bv_options.options \
	datatypes_options.options \
	decision_options.options \
	expr_options.options \
	fp_options.options \
	idl_options.options \
	main_options.options \
	parser_options.options \
	printer_options.options \
	proof_options.options \
	prop_options.options \
	quantifiers_options.options \
	sep_options.options \
	sets_options.options \
	smt_options.options \
	strings_options.options \
	theory_options.options \
	uf_options.options

OPTIONS_SEDS = \
	arith_options.sed \
	arrays_options.sed \
	base_options.sed \
	booleans_options.sed \
	builtin_options.sed \
	bv_options.sed \
	datatypes_options.sed \
	decision_options.sed \
	expr_options.sed \
	fp_options.sed \
	idl_options.sed \
	main_options.sed \
	parser_options.sed \
	printer_options.sed \
	proof_options.sed \
	prop_options.sed \
	quantifiers_options.sed \
	sep_options.sed \
	sets_options.sed \
	smt_options.sed \
	strings_options.sed \
	theory_options.sed \
	uf_options.sed

OPTIONS_HEADS = \
	arith_options.h \
	arrays_options.h \
	base_options.h \
	booleans_options.h \
	builtin_options.h \
	bv_options.h \
	datatypes_options.h \
	decision_options.h \
	expr_options.h \
	fp_options.h \
	idl_options.h \
	main_options.h \
	parser_options.h \
	printer_options.h \
	proof_options.h \
	prop_options.h \
	quantifiers_options.h \
	sep_options.h \
	sets_options.h \
	smt_options.h \
	strings_options.h \
	theory_options.h \
	uf_options.h

OPTIONS_CPPS = \
	arith_options.cpp \
	arrays_options.cpp \
	base_options.cpp \
	booleans_options.cpp \
	builtin_options.cpp \
	bv_options.cpp \
	datatypes_options.cpp \
	decision_options.cpp \
	expr_options.cpp \
	fp_options.cpp \
	idl_options.cpp \
	main_options.cpp \
	parser_options.cpp \
	printer_options.cpp \
	proof_options.cpp \
	prop_options.cpp \
	quantifiers_options.cpp \
	sep_options.cpp \
	sets_options.cpp \
	smt_options.cpp \
	strings_options.cpp \
	theory_options.cpp \
	uf_options.cpp


CPP_TEMPLATE_FILES = \
	base_options_template.h \
	base_options_template.cpp \
	options_holder_template.h \
	options_template.cpp \
	options_get_option_template.cpp \
	options_set_option_template.cpp

CPP_TEMPLATE_SEDS = \
	base_options_template.h.sed \
	base_options_template.cpp.sed \
	options_holder_template.h.sed \
	options_template.cpp.sed \
	options_get_option_template.cpp.sed \
	options_set_option_template.cpp.sed


DOCUMENTATION_FILES = \
	../../doc/cvc4.1 \
	../../doc/libcvc4.3 \
	../../doc/SmtEngine.3cvc \
	../../doc/options.3cvc

DOCUMENTATION_TEMPLATE_FILES = \
	../../doc/cvc4.1_template \
	../../doc/libcvc4.3_template \
	../../doc/SmtEngine.3cvc_template \
	../../doc/options.3cvc_template

DOCUMENTATION_TEMPLATE_SEDS = \
	../../doc/cvc4.1_template.sed \
	../../doc/libcvc4.3_template.sed \
	../../doc/SmtEngine.3cvc_template.sed \
	../../doc/options.3cvc_template.sed

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
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
	theoryof_mode.cpp \
	theoryof_mode.h \
	ufss_mode.h


nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	$(OPTIONS_HEADS) \
	$(OPTIONS_CPPS) \
	options_get_option.cpp \
	options_set_option.cpp


BUILT_SOURCES = \
	$(CPP_TEMPLATE_SEDS) \
	$(DOCUMENTATION_FILES) \
	$(DOCUMENTATION_TEMPLATE_SEDS) \
	$(OPTIONS_CPPS) \
	$(OPTIONS_HEADS) \
	$(OPTIONS_OPTIONS_FILES) \
	$(OPTIONS_SEDS) \
	options.cpp \
	options_get_option.cpp \
	options_set_option.cpp \
	options_holder.h \
	summary.sed


CLEANFILES = \
	$(BUILT_SOURCES) \
	$(DOCUMENTATION_FILES) \
	$(OPTIONS_TEMPS)

EXTRA_DIST = \
	$(DOCUMENTATION_FILES) \
	$(OPTIONS_CPPS) \
	$(OPTIONS_HEADS) \
	$(OPTIONS_SRC_FILES) \
	base_options_template.cpp \
	base_options_template.h \
	language.i \
	mkoptions \
	option_exception.i \
	options.i \
	options_get_option_template.cpp \
	options_holder_template.h \
	options_set_option_template.cpp \
	options_template.cpp





# Make sure the implicit rules never mistake a _template.cpp or _template.h file for source file.
options_holder_template.h options_template.cpp options_get_option_template.cpp options_set_option_template.cpp base_options_template.h base_options_template.cpp :;

# Make sure the implicit rules never mistake X_options for the -o file for a
# CPP file.
arith_options arrays_options base_options booleans_options builtin_options bv_options datatypes_options decision_options expr_options fp_options idl_options main_options parser_options printer_options proof_options prop_options quantifiers_options sep_options sets_options smt_options strings_options theory_options uf_options:;


# These are phony to force them to be made everytime.
.PHONY: arith_options.tmp arrays_options.tmp base_options.tmp booleans_options.tmp builtin_options.tmp bv_options.tmp datatypes_options.tmp decision_options.tmp expr_options.tmp fp_options.tmp idl_options.tmp main_options.tmp parser_options.tmp printer_options.tmp proof_options.tmp prop_options.tmp quantifiers_options.tmp sep_options.tmp sets_options.tmp smt_options.tmp strings_options.tmp theory_options.tmp uf_options.tmp

# Make is happier being listed explictly. Not sure why.
arith_options.tmp arrays_options.tmp base_options.tmp booleans_options.tmp builtin_options.tmp bv_options.tmp datatypes_options.tmp decision_options.tmp expr_options.tmp fp_options.tmp idl_options.tmp main_options.tmp parser_options.tmp printer_options.tmp proof_options.tmp prop_options.tmp quantifiers_options.tmp sep_options.tmp sets_options.tmp smt_options.tmp strings_options.tmp theory_options.tmp uf_options.tmp:
	echo "$@" "$(@:.tmp=)"
	$(AM_V_GEN)(cp "@srcdir@/$(@:.tmp=)" "$@" || true)
#TIM:
#The (... || true) here is to make distcheck not fail.

%_options.options: %_options.tmp
	$(AM_V_GEN)\
	diff -q "$^" "$@" &>/dev/null || mv "$^" "$@" || true


# This bit is kinda tricky.
# We use the updating of %_options.options to signal that the options file updated.
# However, we use the original file in src to generate the file.
%_options.sed: %_options.options mkoptions
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions module-sed "@srcdir@/$(@:.sed=)" ) > "$@"


$(CPP_TEMPLATE_SEDS): %.sed : % mkoptions
#	echo "template seds"
#	echo "$@"
#	echo $(TEMPLATE_SEDS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions template-sed "$<" ) > "$@"

$(DOCUMENTATION_TEMPLATE_SEDS): %.sed : % mkoptions
#	echo "template seds"
#	echo "$@"
#	echo $(TEMPLATE_SEDS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions template-sed "$<" ) > "$@"

%_options.h : %_options.sed mkoptions base_options_template.h base_options_template.h.sed
#	echo heads
#	echo "$@"
#	echo $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/base_options_template.h \
		base_options_template.h.sed \
		"$<" \
	) > "$@"

summary.sed : mkoptions $(OPTIONS_OPTIONS_FILES)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions summary-sed \
		$(OPTIONS_OPTIONS_FILES) \
	) > summary.sed



#   mkoptions apply-sed-to-template sed-file template-file
options_holder.h : options_holder_template.h options_holder_template.h.sed summary.sed mkoptions $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_holder_template.h \
		@builddir@/options_holder_template.h.sed \
		summary.sed \
	) > "$@"

# Make sure not to match with "options.cpp" too.
%_options.cpp: %_options.sed %_options.h mkoptions options_holder.h base_options_template.cpp base_options_template.cpp.sed
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/base_options_template.cpp \
		base_options_template.cpp.sed \
		"$<" \
	) > "$@"




#   mkoptions apply-sed-to-template sed-file template-file
options.cpp : options_template.cpp options_template.cpp.sed mkoptions summary.sed $(OPTIONS_HEADS) options_holder.h
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_template.cpp \
		@builddir@/options_template.cpp.sed \
		summary.sed \
	) > "$@"


#   mkoptions apply-sed-to-template sed-file template-file
options_get_option.cpp : options_get_option_template.cpp options_get_option_template.cpp.sed mkoptions summary.sed $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_get_option_template.cpp \
		@builddir@/options_get_option_template.cpp.sed \
		summary.sed \
	) > "$@"

options_set_option.cpp : options_set_option_template.cpp options_set_option_template.cpp.sed mkoptions summary.sed $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_set_option_template.cpp \
		@builddir@/options_set_option_template.cpp.sed \
		summary.sed \
	) > "$@"



$(DOCUMENTATION_FILES) : % : %_template %_template.sed mkoptions summary.sed
#	echo "$<"
#	echo "$@"
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		"$<" \
		"$<".sed \
		@builddir@/summary.sed \
	) > "$@"



#options-stamp: options_holder_template.h options_template.cpp smt_options_template.cpp base_options_template.h base_options_template.cpp mkoptions $(OPTIONS_FILE_SRCS)


# This rule is ugly.  It's needed to ensure that automake's dependence
# includes are available during distclean, even though they come from
# directories that are cleaned first.  Without this rule, "distclean"
# fails.
%.Plo:; $(MKDIR_P) "$(dir $@)" && : > "$@"
