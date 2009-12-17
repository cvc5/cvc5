if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. "-I@CXXTEST@" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src"
AM_CXXFLGAS_WHITE = -fno-access-control
AM_CXXFLGAS_BLACK =
AM_CXXFLGAS_PUBLIC =
AM_LDFLAGS_WHITE = \
		@abs_top_builddir@/src/context/libcontext.la \
		@abs_top_builddir@/src/expr/libexpr.la \
		@abs_top_builddir@/src/smt/libsmt.la \
		@abs_top_builddir@/src/theory/libtheory.la \
		@abs_top_builddir@/src/util/libutil.la \
		@abs_top_builddir@/src/prop/minisat/libminisat.la
AM_LDFLAGS_BLACK = \
		$(AM_LDFLAGS_WHITE)
AM_LDFLAGS_PUBLIC = \
		@abs_top_builddir@/src/libcvc4.la

TESTS_WHITE = \
	expr/node_white

TESTS_BLACK = \
	expr/node_black

TESTS_PUBLIC =

TESTS = \
	$(TESTS_WHITE) \
	$(TESTS_BLACK) \
	$(TESTS_PUBLIC)

lib_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la

$(TESTS:%=%.cpp): %.cpp: %.h
	mkdir -p `dirname "$@"`
	@CXXTESTGEN@ --have-eh --have-std --error-printer -o "$@" "$<"
$(TESTS_WHITE): %: %.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_WHITE) $@.lo
$(TESTS_BLACK): %: %.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_BLACK) $@.lo
$(TESTS_PUBLIC): %: %.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_PUBLIC) $@.lo

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

endif
