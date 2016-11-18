# All unit tests
UNIT_TESTS = \
	expr/expr_public \
	expr/expr_manager_public \
	expr/type_cardinality_public \
	util/cardinality_public
if WHITE_AND_BLACK_TESTS
UNIT_TESTS += \
	theory/logic_info_white \
	theory/theory_engine_white \
	theory/theory_black \
	theory/theory_white \
	theory/theory_arith_white \
	theory/theory_bv_white \
	theory/type_enumerator_white \
	expr/node_white \
	expr/node_black \
	expr/kind_black \
	expr/kind_map_black \
	expr/node_builder_black \
	expr/node_manager_black \
	expr/node_manager_white \
	expr/attribute_white \
	expr/attribute_black \
	expr/symbol_table_black \
	expr/node_self_iterator_black \
	expr/type_node_white \
	parser/parser_black \
	parser/parser_builder_black \
	prop/cnf_stream_white \
	context/context_black \
	context/context_white \
	context/context_mm_black \
	context/cdo_black \
	context/cdlist_black \
	context/cdlist_context_memory_black \
	context/cdmap_black \
	context/cdmap_white \
	context/cdvector_black \
	context/stacking_vector_black \
	util/array_store_all_black \
	util/assert_white \
	util/binary_heap_black \
	util/bitvector_black \
	util/datatype_black \
	util/configuration_black \
	util/output_black \
	util/exception_black \
	util/integer_black \
	util/integer_white \
	util/listener_black \
	util/rational_black \
	util/rational_white \
	util/stats_black \
	util/boolean_simplification_black \
	util/subrange_bound_white \
	main/interactive_shell_black
endif

export VERBOSE = 1

# Things that aren't tests but that tests rely on and need to
# go into the distribution
TEST_DEPS_DIST = \
	memory.h \
	Makefile.tests

if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. \
	"-I@CXXTEST@" \
	"-I@top_builddir@/src" \
	"-I@top_srcdir@/src/include" \
	"-I@top_srcdir@/lib" \
	"-I@top_srcdir@/src" \
	"-I@top_srcdir@/src/prop/minisat" \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	$(ANTLR_INCLUDES) \
	$(TEST_CPPFLAGS)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas -Wno-parentheses $(TEST_CXXFLAGS)
AM_LDFLAGS = $(TEST_LDFLAGS) $(READLINE_LIBS) $(LIBS)

AM_CXXFLAGS_WHITE = -fno-access-control -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
AM_CXXFLAGS_BLACK = -D__BUILDING_CVC4LIB_UNIT_TEST -D__BUILDING_CVC4PARSERLIB_UNIT_TEST
AM_CXXFLAGS_PUBLIC =
AM_LDFLAGS_WHITE =
AM_LDFLAGS_BLACK =
AM_LDFLAGS_PUBLIC =
AM_LIBADD_WHITE = \
	@abs_top_builddir@/src/main/libmain.a \
	@abs_top_builddir@/src/parser/libcvc4parser.la \
	@abs_top_builddir@/src/libcvc4.la
AM_LIBADD_BLACK = \
	@abs_top_builddir@/src/main/libmain.a \
	@abs_top_builddir@/src/parser/libcvc4parser.la \
	@abs_top_builddir@/src/libcvc4.la
AM_LIBADD_PUBLIC = \
	@abs_top_builddir@/src/parser/libcvc4parser.la \
	@abs_top_builddir@/src/libcvc4.la

EXTRA_DIST = \
	no_cxxtest \
	$(UNIT_TESTS:%=%.cpp) \
	$(UNIT_TESTS:%=%.h) \
	$(TEST_DEPS_DIST)

MOSTLYCLEANFILES = $(UNIT_TESTS) $(UNIT_TESTS:%=%.cpp) $(UNIT_TESTS:%=%.lo)
DISTCLEANFILES = $(UNIT_TESTS:%=@DEPDIR@/%.Plo)

# the tests automake infrastructure doesn't clean up .o files :-(
# handle both .libs and _libs variants
mostlyclean-local:
	@for f in $(UNIT_TESTS); do \
		dir="$$(dirname "$$f")"; fil="$$(basename "$$f")"; \
		for junk in	"$$dir/.libs/$$fil.o" \
				"$$dir/_libs/$$fil.o" \
				"$$dir/.libs/lt-$$fil" \
				"$$dir/_libs/lt-$$fil" \
				"$$dir/.libs/$$fil" \
				"$$dir/_libs/$$fil"; do \
			if test -e "$$junk"; then \
				echo "rm -f \"$$junk\""; \
				rm -f "$$junk"; \
			fi; \
		done; \
	done

@mk_include@ @srcdir@/Makefile.tests

# We leave "TESTS" empty here; it's handled in Makefile.tests (see
# that file for comment)
TESTS = $(UNIT_TESTS)

if STATIC_BINARY
unit_LINK = $(CXXLINK) -all-static
else
unit_LINK = $(CXXLINK)
endif

@AMDEP_TRUE@@am__include@ $(UNIT_TESTS:%=@am__quote@./@DEPDIR@/%.Plo@am__quote@)

$(UNIT_TESTS:%=@am__quote@./@DEPDIR@/%.Plo@am__quote@): %.Plo:
	$(AM_V_at)$(MKDIR_P) `dirname "$@"`
	$(AM_V_GEN)test -e "$@" || touch "$@"

$(UNIT_TESTS:%=@abs_builddir@/%.cpp): @abs_builddir@/%.cpp: %.h
	$(AM_V_at)$(MKDIR_P) `dirname "$@"`
	$(AM_V_GEN)$(CXXTESTGEN) --have-eh --have-std --error-printer -o "$@" "$<"

$(WHITE_TESTS:%=%.lo): %_white.lo: @abs_builddir@/%_white.cpp
@am__fastdepCXX_TRUE@	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -MT $@ -MD -MP -MF $(DEPDIR)/$(@:%.lo=%).Tpo -c -o $@ $<
@am__fastdepCXX_TRUE@	$(AM_V_at)$(am__mv) $(DEPDIR)/$(@:%.lo=%).Tpo $(DEPDIR)/$(@:%.lo=%).Plo
@am__fastdepCXX_FALSE@	$(AM_V_CXX) @AM_BACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	source='$<' object='$@' libtool=yes @AMDEPBACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	DEPDIR=$(DEPDIR) $(CXXDEPMODE) $(depcomp) @AMDEPBACKSLASH@
@am__fastdepCXX_FALSE@	$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@ $<

$(WHITE_TESTS): %_white: %_white.lo $(AM_LIBADD_WHITE)
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LIBADD_WHITE) $(AM_LDFLAGS) $(AM_LDFLAGS_WHITE) $<

$(BLACK_TESTS:%=%.lo): %_black.lo: @abs_builddir@/%_black.cpp
@am__fastdepCXX_TRUE@	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -MT $@ -MD -MP -MF $(DEPDIR)/$(@:%.lo=%).Tpo -c -o $@ $<
@am__fastdepCXX_TRUE@	$(AM_V_at)$(am__mv) $(DEPDIR)/$(@:%.lo=%).Tpo $(DEPDIR)/$(@:%.lo=%).Plo
@am__fastdepCXX_FALSE@	$(AM_V_CXX) @AM_BACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	source='$<' object='$@' libtool=yes @AMDEPBACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	DEPDIR=$(DEPDIR) $(CXXDEPMODE) $(depcomp) @AMDEPBACKSLASH@
@am__fastdepCXX_FALSE@	$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@ $<

$(BLACK_TESTS): %_black: %_black.lo $(AM_LIBADD_BLACK)
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LIBADD_BLACK) $(AM_LDFLAGS) $(AM_LDFLAGS_BLACK) $<

$(PUBLIC_TESTS:%=%.lo): %_public.lo: @abs_builddir@/%_public.cpp
@am__fastdepCXX_TRUE@	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -MT $@ -MD -MP -MF $(DEPDIR)/$(@:%.lo=%).Tpo -c -o $@ $<
@am__fastdepCXX_TRUE@	$(AM_V_at)$(am__mv) $(DEPDIR)/$(@:%.lo=%).Tpo $(DEPDIR)/$(@:%.lo=%).Plo
@am__fastdepCXX_FALSE@	$(AM_V_CXX) @AM_BACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	source='$<' object='$@' libtool=yes @AMDEPBACKSLASH@
@AMDEP_TRUE@@am__fastdepCXX_FALSE@	DEPDIR=$(DEPDIR) $(CXXDEPMODE) $(depcomp) @AMDEPBACKSLASH@
@am__fastdepCXX_FALSE@	$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@ $<

$(PUBLIC_TESTS): %_public: %_public.lo $(AM_LIBADD_PUBLIC)
	$(AM_V_CXXLD)$(unit_LINK) $(AM_LIBADD_PUBLIC) $(AM_LDFLAGS) $(AM_LDFLAGS_PUBLIC) $<

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

EXTRA_DIST = \
	no_cxxtest \
	$(UNIT_TESTS:%=%.h) \
	$(TEST_DEPS_DIST) \
	no-cxxtest-available

endif

$(UNIT_TESTS:%=%.cpp): $(UNIT_TESTS:%=@abs_builddir@/%.cpp)

# trick automake into setting LTCXXCOMPILE, CXXLINK, etc.
if CVC4_FALSE
noinst_LTLIBRARIES = libdummy.la
nodist_libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la
endif

# synonyms for "check" in this directory in this directory
.PHONY: units test
units test: check

# no-ops here
.PHONY: systemtests regress regress0 regress1 regress2 regress3 regress4
regress regress0 regress1 regress2 regress3 regress4:

if HAVE_CXXTESTGEN
# all is fine with the world
else
# all is not !
no-cxxtest-available:
	@if test "$(I_REALLY_WANT_TO_BUILD_CVC4_DIST_WITHOUT_TESTS)" = 1; then \
		echo; \
		echo "WARNING:"; \
		echo "WARNING: No CxxTest to build unit tests, but, then, you know that;"; \
		echo "WARNING: I hope you know what you're doing."; \
		echo "WARNING:"; \
		echo; \
		( echo "CxxTest was not available at the time this distribution was built,"; \
		  echo "so the tests could not be built.  You'll need CxxTest to test this"; \
		  echo "distribution." ) >no-cxxtest-available; \
	else \
		echo; \
		echo "ERROR:"; \
		echo "ERROR: You cannot make dist in this build directory, you do not have CxxTest."; \
		echo "ERROR: The tests should be generated for the user and included in the tarball,"; \
		echo "ERROR: otherwise they'll be required to have CxxTest just to test the standard"; \
		echo "ERROR: distribution built correctly."; \
		echo "ERROR: If you really want to do this, append the following to your make command."; \
		echo "ERROR:"; \
		echo "ERROR:     I_REALLY_WANT_TO_BUILD_CVC4_DIST_WITHOUT_TESTS=1"; \
		echo "ERROR:"; \
		echo; \
		exit 1; \
	fi >&2
endif

