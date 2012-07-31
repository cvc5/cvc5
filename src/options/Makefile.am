OPTIONS_FILES = \
	options/base_options \
	expr/options \
	theory/booleans/options \
	theory/options \
	theory/bv/options \
	theory/datatypes/options \
	theory/builtin/options \
	theory/arith/options \
	theory/uf/options \
	theory/arrays/options \
	theory/quantifiers/options \
	theory/rewriterules/options \
	prop/options \
	proof/options \
	printer/options \
	smt/options \
	decision/options \
	main/options \
	parser/options

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = liboptions.la

liboptions_la_SOURCES = \
	options.h \
	base_options_handlers.h

nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	$(OPTIONS_FILES:%=../%.cpp) \
	$(OPTIONS_FILES:%=../%.h)
nodist_liboptions_la_OBJECTS = \
	$(patsubst %.cpp,%.lo,$(filter %.cpp,$(nodist_liboptions_la_SOURCES)))

BUILT_SOURCES = \
	options.cpp \
	options_holder.h \
	base_options.cpp \
	base_options.h \
	../smt/smt_options.cpp \
	$(OPTIONS_FILES:%=../%.cpp) \
	$(OPTIONS_FILES:%=../%.h) \
	exprs-builts

DISTCLEANFILES = \
	$(BUILT_SOURCES) \
	options-stamp

EXTRA_DIST = \
	mkoptions \
	base_options \
	base_options_template.h \
	base_options_template.cpp \
	options_template.cpp \
	options_holder_template.h \
	options.i \
	$(OPTIONS_FILES:%=../%)

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
	grep '\<$(@:_tags.tmp=) *( *\".*\" *)' \
		`find @srcdir@/../ -name "*.cpp" -or -name "*.h" -or -name "*.cc" -or -name "*.g"` | \
	sed 's/^$(@:_tags.tmp=) *( *\"\([^"]*\)\".*/\1/;s/.*[^a-zA-Z0-9_]$(@:_tags.tmp=) *( *\"\([^"]*\)\".*/\1/' | sort | uniq >"$@"

MOSTLYCLEANFILES = \
	Debug_tags \
	Trace_tags \
	Debug_tags.tmp \
	Trace_tags.tmp \
	Debug_tags.h \
	Trace_tags.h

options_holder.h options.cpp ../smt/smt_options.cpp base_options.cpp base_options.h $(OPTIONS_FILES:%=../%.cpp) $(OPTIONS_FILES:%=../%.h): options-stamp
options-stamp: options_holder_template.h options_template.cpp ../smt/smt_options_template.cpp base_options_template.h base_options_template.cpp mkoptions $(OPTIONS_FILES:%=../%)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions \
		@srcdir@/options_holder_template.h @srcdir@/options_holder.h \
		@srcdir@/options_template.cpp @srcdir@/options.cpp \
		@srcdir@/../smt/smt_options_template.cpp @srcdir@/../smt/smt_options.cpp \
		@top_builddir@/doc/cvc4.1_template @top_builddir@/doc/cvc4.1 \
		-t \
		@srcdir@/base_options_template.h @srcdir@/base_options_template.cpp \
		$(foreach o,$(OPTIONS_FILES),"$(srcdir)/../$(o)" "$(dir $(srcdir)/../$(o))") \
	)
	touch "$@"

base_options $(OPTIONS_FILES:%=../%):;

.PHONY: exprs-builts
exprs-builts:; $(AM_V_at)[ "$(FROM_EXPR)" != 1 ] && $(MAKE) -C ../expr builts || true
