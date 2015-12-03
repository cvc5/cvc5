OPTIONS_FILES_SRCS = \
	base_options.cpp \
	base_options.h \
	../expr/options.cpp \
	../expr/options.h \
	../theory/booleans/options.cpp \
	../theory/booleans/options.h \
	../theory/options.cpp \
	../theory/options.h \
	../theory/bv/options.cpp \
	../theory/bv/options.h \
	../theory/datatypes/options.cpp \
	../theory/datatypes/options.h \
	../theory/builtin/options.cpp \
	../theory/builtin/options.h \
	../theory/arith/options.cpp \
	../theory/arith/options.h \
	../theory/uf/options.cpp \
	../theory/uf/options.h \
	../theory/arrays/options.cpp \
	../theory/arrays/options.h \
	../theory/quantifiers/options.cpp \
	../theory/quantifiers/options.h \
	../theory/strings/options.cpp \
	../theory/strings/options.h \
	../prop/options.cpp \
	../prop/options.h \
	../proof/options.cpp \
	../proof/options.h \
	../printer/options.cpp \
	../printer/options.h \
	../smt/options.cpp \
	../smt/options.h \
	../decision/options.cpp \
	../decision/options.h \
	../main/options.cpp \
	../main/options.h \
	../parser/options.cpp \
	../parser/options.h \
	../theory/idl/options.cpp \
	../theory/idl/options.h \
	../theory/sets/options.cpp \
	../theory/sets/options.h \
	../theory/fp/options.cpp \
	../theory/fp/options.h

OPTIONS_FILES = \
	$(patsubst %.cpp,%,$(filter %.cpp,$(OPTIONS_FILES_SRCS)))

OPTIONS_CPPS = \
	$(filter %.cpp,$(OPTIONS_FILES_SRCS))

OPTIONS_HEADS = \
	$(filter %.h,$(OPTIONS_FILES_SRCS))

OPTIONS_SEDS = \
	$(patsubst %,%.sed,$(OPTIONS_FILES))

OPTIONS_OBJ = \
	$(patsubst %.cpp,%.$(OBJEXT),$(OPTIONS_CPP))




DOCUMENTATION_FILES = \
	../../doc/cvc4.1 \
	../../doc/libcvc4.3 \
	../../doc/SmtEngine.3cvc \
	../../doc/options.3cvc

TEMPLATE_FILES = \
	base_options_template.h \
	base_options_template.cpp \
	options_holder_template.h \
	options_template.cpp \
	../smt/smt_options_template.cpp \
	../../doc/cvc4.1_template \
	../../doc/libcvc4.3_template \
	../../doc/SmtEngine.3cvc_template \
	../../doc/options.3cvc_template

TEMPLATE_SEDS = \
	$(patsubst %,%.sed,$(TEMPLATE_FILES))

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = liboptions.la

liboptions_la_SOURCES = \
	options.h \
	base_options_handlers.h \
	option_exception.h

nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	$(OPTIONS_FILES_SRCS)


BUILT_SOURCES = \
	exprs-builts \
	../smt/smt_options.cpp \
	options.cpp \
	options_holder.h \
	$(OPTIONS_FILES_SRCS) \
	$(OPTIONS_SEDS) \
	summary.sed \
	$(TEMPLATE_SEDS)


# The documentation files are added to BUILT_SOURCES to get the files to
# be built. Alternative suggestions for building these files would be
# appreciated.
BUILT_SOURCES += \
	$(DOCUMENTATION_FILES)


CLEANFILES = \
	$(OPTIONS_FILES_SRCS) \
	$(BUILT_SOURCES) \
	$(DOCUMENTATION_FILES)

EXTRA_DIST = \
	mkoptions \
	base_options_template.h \
	base_options_template.cpp \
	options_template.cpp \
	options_holder_template.h \
	options.i \
	option_exception.i \
	$(OPTIONS_FILES) \
	mktagheaders \
	mktags \
	$(DOCUMENTATION_FILES)


# listing {Debug,Trace}_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES += \
	Debug_tags.h \
	Debug_tags \
	Trace_tags.h \
	Trace_tags

%_tags.h: %_tags mktagheaders
	$(AM_V_at)chmod +x @srcdir@/mktagheaders
	$(AM_V_GEN)( @srcdir@/mktagheaders "$<" "$<" ) >"$@"

# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
%_tags: %_tags.tmp
	$(AM_V_GEN)\
	diff -q "$^" "$@" &>/dev/null || mv "$^" "$@" || true
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: Debug_tags.tmp Trace_tags.tmp
# The "sed" invocation below is particularly obnoxious, but it works around
# inconsistencies in REs on different platforms, using only a basic regular
# expression (no |, no \<, ...).
Debug_tags.tmp Trace_tags.tmp: mktags
	$(AM_V_at)chmod +x @srcdir@/mktags
	$(AM_V_GEN)(@srcdir@/mktags \
    '$(@:_tags.tmp=)' \
    "$$(find @srcdir@/../ -name '*.cpp' -o -name '*.h' -o -name '*.cc' -o -name '*.g')") >"$@"

MOSTLYCLEANFILES = \
	Debug_tags \
	Trace_tags \
	Debug_tags.tmp \
	Trace_tags.tmp \
	Debug_tags.h \
	Trace_tags.h

#   mkoptions template-sed template-file (options-file)*
#   mkoptions apply-sed-files-to-template sed-file template-file filename

$(OPTIONS_FILES):;
options_holder_template.h options_template.cpp ../smt/smt_options_template.cpp base_options_template.h base_options_template.cpp :;


$(TEMPLATE_SEDS) : %.sed : % mkoptions
#	echo "template seds"
#	echo "$@"
#	echo $(TEMPLATE_SEDS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions template-sed "$<" ) > "$@"


$(OPTIONS_SEDS) : %.sed : % mkoptions
#	echo "sedheads"
#	echo "$@"
#	echo $(OPTIONS_SEDS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)mkdir -p `dirname "$@"`
	$(AM_V_GEN)(@srcdir@/mkoptions module-sed "$<" ) > "$@"

$(OPTIONS_HEADS) : %.h : %.sed mkoptions base_options_template.h base_options_template.h.sed
#	echo heads
#	echo "$@"
#	echo $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)mkdir -p `dirname "$@"`
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/base_options_template.h \
		base_options_template.h.sed \
		"$<" \
	) > "$@"

summary.sed : mkoptions $(OPTIONS_FILES)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions summary-sed \
		$(foreach o,$(OPTIONS_FILES),"$(srcdir)/$(o)") \
	) > summary.sed



#   mkoptions apply-sed-to-template sed-file template-file
options_holder.h : options_holder_template.h options_holder_template.h.sed summary.sed mkoptions
#	echo "$(OPTIONS_FILES)"
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_holder_template.h \
		@builddir@/options_holder_template.h.sed \
		summary.sed \
	) > "$@"

gen-heads-stamp : $(OPTIONS_HEADS) options_holder.h
.PHONY : gen-heads-stamp


# Bit of a hack here. The .h file needs to always be built before the .cpp file is compiled.
$(OPTIONS_CPPS) : %.cpp : %.sed mkoptions base_options_template.cpp base_options_template.cpp.sed gen-heads-stamp
#	echo "cpps"
#	echo "$@"
#	echo "$<"
#	echo $(OPTIONS_CPPS)
#	echo $(OPTIONS_FILES_SRCS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_at)mkdir -p `dirname "$@"`
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/base_options_template.cpp \
		base_options_template.cpp.sed \
		"$<" \
	) > "$@"



#   mkoptions apply-sed-to-template sed-file template-file
options.cpp : options_template.cpp options_template.cpp.sed mkoptions summary.sed gen-heads-stamp
#	echo "$(OPTIONS_FILES)"
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_template.cpp \
		@builddir@/options_template.cpp.sed \
		summary.sed \
	) > "$@"


#   mkoptions apply-sed-to-template sed-file template-file
../smt/smt_options.cpp : ../smt/smt_options_template.cpp ../smt/smt_options_template.cpp.sed mkoptions summary.sed gen-heads-stamp
#	echo "$(OPTIONS_FILES)"
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/../smt/smt_options_template.cpp \
		@builddir@/../smt/smt_options_template.cpp.sed \
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



#options-stamp: options_holder_template.h options_template.cpp ../smt/smt_options_template.cpp base_options_template.h base_options_template.cpp mkoptions $(OPTIONS_FILE_SRCS)


# This rule is ugly.  It's needed to ensure that automake's dependence
# includes are available during distclean, even though they come from
# directories that are cleaned first.  Without this rule, "distclean"
# fails.
%.Plo:; $(MKDIR_P) "$(dir $@)" && : > "$@"

# Tim:
# This is insanely ugly and brittle!
# *Any* proposal to clean this up is welcomed!
# We are overloading automake's default distclean here. We have to overload
# distclean because otherwise it deletes the dependency directory
# "src/expr/.deps", then when running make distclean in src/expr it attempts to
# include .Plo files "defined in src/expr/.deps".
# An example from src/expr/Makefile.ina :
# @AMDEP_TRUE@@am__include@ @am__quote@./$(DEPDIR)/attribute.Plo@am__quote@
# The include must fail because this make file deleted that directory and
# distclean cannot proceed. So we override distclean to only remove
# "-rm -rf ./$(DEPDIR)". We then do manual massaging to finish up removing the
# extra files. To reproduce this, you can comment out the distclean below, run
# a distcheck and repeat this process.
# Why was this not a problem before? I do not know.
MANUAL_RM = \
	$(CLEANFILES) \
	../main/.dirstamp \
	../expr/.dirstamp \
	../options/options.lo \
	../options/base_options.lo \
	../options/.libs/options.o \
	../options/.libs/base_options.o \
	../options/.libs/liboptions.a \
	../options/Trace_tags.tmp \
	../options/Debug_tags.tmp \
	../options/liboptions.la \
	../parser/.dirstamp




distclean:
	-rm -rf ./$(DEPDIR)
	-rm -f Makefile
	-rm -f $(MANUAL_RM)

.PHONY: exprs-builts
exprs-builts:; $(AM_V_at)[ "$(FROM_EXPR)" != 1 ] && $(MAKE) -C ../expr builts || true

