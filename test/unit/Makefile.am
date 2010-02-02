# All unit tests
UNIT_TESTS = \
	expr/node_white \
	expr/node_black \
	parser/parser_black \
	context/context_black

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

@mk_include@ @srcdir@/Makefile.tests

if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. "-I@CXXTEST@" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src" \
	$(TEST_CPPFLAGS)
AM_CXXFLAGS = $(TEST_CXXFLAGS)
AM_LDFLAGS = $(TEST_LDFLAGS)

AM_CXXFLAGS_WHITE = -fno-access-control
AM_CXXFLAGS_BLACK =
AM_CXXFLAGS_PUBLIC =
AM_LDFLAGS_WHITE = \
	@abs_top_builddir@/src/parser/libcvc4parser_noinst.la \
	@abs_top_builddir@/src/libcvc4_noinst.la
AM_LDFLAGS_BLACK = \
	@abs_top_builddir@/src/parser/libcvc4parser_noinst.la \
	@abs_top_builddir@/src/libcvc4_noinst.la
AM_LDFLAGS_PUBLIC = \
	@abs_top_builddir@/src/libcvc4.la

TESTS = $(UNIT_TESTS)

EXTRA_DIST = \
	no_cxxtest \
	$(TEST_DEPS_DIST)

# without these here, LTCXXCOMPILE, CXXLINK, etc., aren't set :-(
noinst_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la

$(TESTS:%=%.cpp): %.cpp: %.h
	mkdir -p `dirname "$@"`
	@CXXTESTGEN@ --have-eh --have-std --error-printer -o "$@" "$<"
$(WHITE_TESTS): %_white: %_white.cpp $(TEST_DEPS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_WHITE) $@.lo
$(BLACK_TESTS): %_black: %_black.cpp $(TEST_DEPS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_BLACK) $@.lo
$(PUBLIC_TESTS): %_public: %_public.cpp $(TEST_DEPS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_PUBLIC) $@.lo

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

EXTRA_DIST = \
	$(UNIT_TESTS) \
	$(TEST_DEPS_DIST)

endif

# synonyms for "check"
.PHONY: regress regress0 regress1 regress2 regress3 test
regress regress0 regress1 regress2 regress3 test: check
