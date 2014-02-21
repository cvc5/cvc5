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
	../theory/rewriterules/options.cpp \
	../theory/rewriterules/options.h \
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
	../theory/sets/options.h

OPTIONS_FILES = \
	$(patsubst %.cpp,%,$(filter %.cpp,$(OPTIONS_FILES_SRCS)))

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
	../theory/rewriterules/options.cpp \
	../theory/rewriterules/options.h \
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
	../theory/sets/options.h

BUILT_SOURCES = \
	exprs-builts \
	../smt/smt_options.cpp \
	options.cpp \
	options_holder.h

CLEANFILES = \
	$(OPTIONS_FILES_SRCS) \
	$(BUILT_SOURCES) \
	options-stamp

EXTRA_DIST = \
	mkoptions \
	base_options_template.h \
	base_options_template.cpp \
	options_template.cpp \
	options_holder_template.h \
	options.i \
	option_exception.i \
	$(OPTIONS_FILES) \
	options-stamp \
	../smt/smt_options.cpp \
	options.cpp \
	options_holder.h \
	$(OPTIONS_FILES_SRCS)

if CVC4_DEBUG
# listing Debug_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES += \
	Debug_tags.h \
	Debug_tags
endif
if CVC4_TRACING
# listing Trace_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES += \
	Trace_tags.h \
	Trace_tags
endif
%_tags.h: %_tags
	$(AM_V_GEN)( \
	  echo 'static char const* const $^[] = {'; \
	  for tag in `cat $^`; do \
	    echo "\"$$tag\","; \
	  done; \
	  echo 'NULL'; \
	  echo '};' \
	) >"$@"

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
Debug_tags.tmp Trace_tags.tmp:
	$(AM_V_GEN)\
	grep '\<$(@:_tags.tmp=)\(\.isOn\)* *( *\".*\" *)' \
		`find @srcdir@/../ -name "*.cpp" -o -name "*.h" -o -name "*.cc" -o -name "*.g"` | \
	sed 's/^$(@:_tags.tmp=)\(\.isOn\)* *( *\"\([^"]*\)\".*/\2/;s/.*[^a-zA-Z0-9_]$(@:_tags.tmp=)\(\.isOn\)* *( *\"\([^"]*\)\".*/\2/' | LC_ALL=C sort | uniq >"$@"

MOSTLYCLEANFILES = \
	Debug_tags \
	Trace_tags \
	Debug_tags.tmp \
	Trace_tags.tmp \
	Debug_tags.h \
	Trace_tags.h

options_holder.h options.cpp ../smt/smt_options.cpp $(OPTIONS_FILES_SRCS): options-stamp
options-stamp: options_holder_template.h options_template.cpp ../smt/smt_options_template.cpp base_options_template.h base_options_template.cpp mkoptions $(OPTIONS_FILES)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions \
		@srcdir@/options_holder_template.h @builddir@/options_holder.h \
		@srcdir@/options_template.cpp @builddir@/options.cpp \
		@srcdir@/../smt/smt_options_template.cpp @builddir@/../smt/smt_options.cpp \
		@top_builddir@/doc/cvc4.1_template @top_builddir@/doc/cvc4.1 \
		@top_builddir@/doc/libcvc4.3_template @top_builddir@/doc/libcvc4.3 \
		@top_builddir@/doc/SmtEngine.3cvc_template @top_builddir@/doc/SmtEngine.3cvc \
		@top_builddir@/doc/options.3cvc_template @top_builddir@/doc/options.3cvc \
		-t \
		@srcdir@/base_options_template.h @srcdir@/base_options_template.cpp \
		$(foreach o,$(OPTIONS_FILES),"$(srcdir)/$(o)" "$(patsubst %/,%,$(dir $(o)))") \
	)
	touch "$@"

$(OPTIONS_FILES):;

# This rule is ugly.  It's needed to ensure that automake's dependence
# includes are available during distclean, even though they come from
# directories that are cleaned first.  Without this rule, "distclean"
# fails.
%.Plo:; $(MKDIR_P) "$(dir $@)" && : > "$@"

.PHONY: exprs-builts
exprs-builts:; $(AM_V_at)[ "$(FROM_EXPR)" != 1 ] && $(MAKE) -C ../expr builts || true
