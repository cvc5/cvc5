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
	expr/declaration_scope_black \
	parser/parser_black \
	prop/cnf_stream_black \
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
	util/bitvector_black \
	util/configuration_black \
	util/output_black \
	util/exception_black \
	util/integer_black \
	util/integer_white \
	util/rational_black \
    util/rational_white

# Things that aren't tests but that tests rely on and need to
# go into the distribution
TEST_DEPS_DIST = \
	memory.h

if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. "-I@CXXTEST@" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src" \
	$(ANTLR_INCLUDES) $(TEST_CPPFLAGS)
AM_CXXFLAGS = -Wall $(TEST_CXXFLAGS)
AM_LDFLAGS = $(TEST_LDFLAGS)

AM_CXXFLAGS_WHITE = -fno-access-control -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
AM_CXXFLAGS_BLACK = -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
AM_CXXFLAGS_PUBLIC =
AM_LDFLAGS_WHITE =
AM_LDFLAGS_BLACK =
AM_LDFLAGS_PUBLIC =
AM_LIBADD_WHITE = \
	@abs_top_builddir@/src/parser/libcvc4parser_noinst.la \
	@abs_top_builddir@/src/libcvc4_noinst.la
AM_LIBADD_BLACK = \
	@abs_top_builddir@/src/parser/libcvc4parser_noinst.la \
	@abs_top_builddir@/src/libcvc4_noinst.la
AM_LIBADD_PUBLIC = \
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

@AMDEP_TRUE@@am__include@ $(UNIT_TESTS:%=@am__quote@./$(DEPDIR)/%.Plo@am__quote@)

$(UNIT_TESTS:%=@am__quote@./$(DEPDIR)/%.Plo@am__quote@): %.Plo:
	$(AM_V_at)$(MKDIR_P) `dirname "$@"`
	$(AM_V_GEN)test -e "$@" || touch "$@"

$(UNIT_TESTS:%=%.cpp): %.cpp: %.h
	$(AM_V_at)$(MKDIR_P) `dirname "$@"`
	$(AM_V_GEN)$(CXXTESTGEN) --have-eh --have-std --error-printer -o "$@" "$<"

$(WHITE_TESTS:%=%.lo): %_white.lo: %_white.cpp
@am__fastdepCXX_TRUE@	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -MT $@ -MD -MP -MF $(DEPDIR)/$(@:%.lo=%).Tpo -c -o $@ $<
@am__fastdepCXX_TRUE@	$(AM_V_at)$(am__mv) $(DEPDIR)/$(@:%.lo=%).Tpo $(DEPDIR)/$(@:%.lo=%).Plo
@am__fastdepCXX_FALSE@	$(AM_V_CXX) @AM_BACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	source='$<' object='$@' libtool=yes @AMDEPBACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	DEPDIR=$(DEPDIR) $(CXXDEPMODE) $(depcomp) @AMDEPBACKSLASH@
@am__fastdepCXX_FALSE@	$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@ $<

$(WHITE_TESTS): %_white: %_white.lo $(AM_LIBADD_WHITE)
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LIBADD_WHITE) $(AM_LDFLAGS_WHITE) $<

$(BLACK_TESTS:%=%.lo): %_black.lo: %_black.cpp
@am__fastdepCXX_TRUE@	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -MT $@ -MD -MP -MF $(DEPDIR)/$(@:%.lo=%).Tpo -c -o $@ $<
@am__fastdepCXX_TRUE@	$(AM_V_at)$(am__mv) $(DEPDIR)/$(@:%.lo=%).Tpo $(DEPDIR)/$(@:%.lo=%).Plo
@am__fastdepCXX_FALSE@	$(AM_V_CXX) @AM_BACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	source='$<' object='$@' libtool=yes @AMDEPBACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	DEPDIR=$(DEPDIR) $(CXXDEPMODE) $(depcomp) @AMDEPBACKSLASH@
@am__fastdepCXX_FALSE@	$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@ $<

$(BLACK_TESTS): %_black: %_black.lo $(AM_LIBADD_BLACK)
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LIBADD_BLACK) $(AM_LDFLAGS_BLACK) $<

$(PUBLIC_TESTS:%=%.lo): %_public.lo: %_public.cpp
@am__fastdepCXX_TRUE@	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -MT $@ -MD -MP -MF $(DEPDIR)/$(@:%.lo=%).Tpo -c -o $@ $<
@am__fastdepCXX_TRUE@	$(AM_V_at)$(am__mv) $(DEPDIR)/$(@:%.lo=%).Tpo $(DEPDIR)/$(@:%.lo=%).Plo
@am__fastdepCXX_FALSE@	$(AM_V_CXX) @AM_BACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	source='$<' object='$@' libtool=yes @AMDEPBACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	DEPDIR=$(DEPDIR) $(CXXDEPMODE) $(depcomp) @AMDEPBACKSLASH@
@am__fastdepCXX_FALSE@	$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@ $<

$(PUBLIC_TESTS): %_public: %_public.lo $(AM_LIBADD_PUBLIC)
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LIBADD_PUBLIC) $(AM_LDFLAGS_PUBLIC) $<

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
