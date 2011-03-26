TESTS_ENVIRONMENT =
TESTS = \
	boilerplate \
	ouroborous

# Things that aren't tests but that tests rely on and need to
# go into the distribution
TEST_DEPS_DIST =

# Make-level dependencies; these don't go in the source distribution
# but should trigger a re-compile of all unit tests.  Libraries are
# included here because (1) if static-linking, the tests must be
# relinked, and (2) if they've changed that means the sources changed,
# and that means we should ensure the tests compile against any
# changes made in the header files.
TEST_DEPS_NODIST = \
	$(abs_top_builddir)/src/libcvc4.la \
	$(abs_top_builddir)/src/parser/libcvc4parser.la

TEST_DEPS = \
	$(TEST_DEPS_DIST) \
	$(TEST_DEPS_NODIST)

EXTRA_DIST = \
	$(TEST_DEPS_DIST)

if STATIC_BINARY
system_LINK = $(CXXLINK) -all-static
else
system_LINK = $(CXXLINK)
endif

AM_CPPFLAGS = \
	-I. \
	"-I@top_srcdir@/src/include" \
	"-I@top_srcdir@/lib" \
	"-I@top_srcdir@/src" \
	"-I@top_builddir@/src" \
	"-I@top_srcdir@/src/prop/minisat" \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	$(TEST_CPPFLAGS)
LIBADD = \
	@abs_top_builddir@/src/parser/libcvc4parser.la \
	@abs_top_builddir@/src/libcvc4.la

# WHEN SYSTEM TESTS ARE ADDED, BUILD LIKE THIS:
$(TESTS:%=%.lo): %.lo: %.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS) -c -o $@ $+
$(TESTS): %: %.lo $(LIBADD)
	$(AM_V_CXXLD)$(system_LINK) $(LIBADD) $(AM_LDFLAGS) $<

# trick automake into setting LTCXXCOMPILE, CXXLINK, etc.
if CVC4_FALSE
noinst_LTLIBRARIES = libdummy.la
nodist_libdummy_la_SOURCES = ouroborous.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la
endif

# rebuild tests if a library changes
#$(TESTS):: $(TEST_DEPS)

MAKEFLAGS = -k
export VERBOSE = 1

# synonyms for "check" in this directory in this directory
.PHONY: test systemtests
test systemtests: check

# no-ops here
.PHONY: units regress regress0 regress1 regress2 regress3
units regress regress0 regress1 regress2 regress3:
