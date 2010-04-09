# All unit tests
UNIT_TESTS = \
	expr/expr_public \
	expr/node_white \
	expr/node_black \
	expr/kind_black \
	expr/node_builder_black \
	expr/node_manager_black \
	expr/node_manager_white \
	expr/attribute_white \
	expr/attribute_black \
	parser/parser_white \
	context/context_black \
	context/context_white \
	context/context_mm_black \
	context/cdo_black \
	context/cdlist_black \
	context/cdmap_black \
	context/cdmap_white \
	theory/theory_black \
	theory/theory_uf_white \
	util/assert_white \
	util/configuration_black \
	util/output_black \
	util/exception_black \
	util/integer_black \
	util/integer_white \
	util/rational_white

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

if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. "-I@CXXTEST@" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src" \
	$(TEST_CPPFLAGS)
AM_CXXFLAGS = -Wall $(TEST_CXXFLAGS)
AM_LDFLAGS = $(TEST_LDFLAGS)

AM_CXXFLAGS_WHITE = -fno-access-control -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
AM_CXXFLAGS_BLACK = -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
AM_CXXFLAGS_PUBLIC =
AM_LDFLAGS_WHITE = \
	@abs_top_builddir@/src/parser/libcvc4parser_noinst.la \
	@abs_top_builddir@/src/libcvc4_noinst.la
AM_LDFLAGS_BLACK = \
	@abs_top_builddir@/src/parser/libcvc4parser_noinst.la \
	@abs_top_builddir@/src/libcvc4_noinst.la
AM_LDFLAGS_PUBLIC = \
	@abs_top_builddir@/src/libcvc4.la

EXTRA_DIST = \
	no_cxxtest \
	$(TEST_DEPS_DIST)

MOSTLYCLEANFILES = $(UNIT_TESTS) $(UNIT_TESTS:%=%.cpp)

@mk_include@ @srcdir@/Makefile.tests

# We leave "TESTS" empty here; it's handled in Makefile.tests (see
# that file for comment)
# TESTS =

if STATIC_BINARY
unit_LINK = $(CXXLINK) -all-static
else
unit_LINK = $(CXXLINK)
endif

$(UNIT_TESTS:%=%.cpp): %.cpp: %.h
	$(AM_V_at)mkdir -p `dirname "$@"`
	$(AM_V_GEN)$(CXXTESTGEN) --have-eh --have-std --error-printer -o "$@" "$<"
$(WHITE_TESTS): %_white: %_white.cpp $(TEST_DEPS)
	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@.lo @abs_builddir@/$<
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LDFLAGS_WHITE) $@.lo
$(BLACK_TESTS): %_black: %_black.cpp $(TEST_DEPS)
	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@.lo @abs_builddir@/$<
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LDFLAGS_BLACK) $@.lo
$(PUBLIC_TESTS): %_public: %_public.cpp $(TEST_DEPS)
	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@.lo @abs_builddir@/$<
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LDFLAGS_PUBLIC) $@.lo

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

EXTRA_DIST = \
	$(UNIT_TESTS:%=%.cpp) \
	$(TEST_DEPS_DIST)

endif

# trick automake into setting LTCXXCOMPILE, CXXLINK, etc.
if CVC4_FALSE
noinst_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la
endif

# synonyms for "check"
.PHONY: regress test
regress test: check

# in unit test dir, regressN are also synonyms for check
.PHONY: regress0 regress1 regress2 regress3
regress0 regress1 regress2 regress3: check
