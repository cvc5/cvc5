AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbase.la

# Do not list built sources here!
# Rather, list them under BUILT_SOURCES, and their .in versions under
# EXTRA_DIST.  Otherwise, they're packaged up in the tarball, which is
# no good---they belong in the configured builds/ directory.  If they
# end up in the source directory, they build the cvc4 that was
# configured at the time of the "make dist", which (1) may not be the
# configuration that the user wants, and (2) might cause link errors.
libbase_la_SOURCES = \
	Makefile.am \
	Makefile.in \
	configuration.cpp \
	configuration.h \
	configuration_private.h \
	cvc4_assert.cpp \
	cvc4_assert.h \
	cvc4_check.cpp \
	cvc4_check.h \
	exception.cpp \
	exception.h \
	listener.cpp \
	listener.h \
	modal_exception.h \
	output.cpp \
	output.h \
	tls.h

# listing {Debug,Trace}_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES = \
	Debug_tags.h \
	Debug_tags \
	Trace_tags.h \
	Trace_tags

MOSTLYCLEANFILES = \
	Debug_tags \
	Trace_tags \
	Debug_tags.tmp \
	Trace_tags.tmp \
	Debug_tags.h \
	Trace_tags.h

EXTRA_DIST = \
	configuration.i \
	exception.i \
	mktagheaders \
	mktags \
	modal_exception.i

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
