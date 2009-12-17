if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. "-I@CXXTEST@" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src"
AM_LDFLAGS = \
		@abs_top_builddir@/src/context/libcontext.la \
		@abs_top_builddir@/src/expr/libexpr.la \
		@abs_top_builddir@/src/smt/libsmt.la \
		@abs_top_builddir@/src/theory/libtheory.la \
		@abs_top_builddir@/src/util/libutil.la \
		@abs_top_builddir@/src/prop/minisat/libminisat.la

TESTS_WHITE = \
	expr/node_white

TESTS_BLACK = \
	expr/node_black

TESTS = \
	$(TESTS_WHITE) \
	$(TESTS_BLACK)

lib_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la

$(TESTS:%=%.cpp): %.cpp: %.h
	mkdir -p `dirname "$@"`
	@CXXTESTGEN@ --have-eh --have-std --error-printer -o "$@" "$<"
$(TESTS_WHITE): %: %.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) -c -fno-access-control -o $@.lo $<
	$(CXXLINK) $@.lo
$(TESTS_BLACK): %: %.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) -c -o $@.lo $<
	$(CXXLINK) $@.lo

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

endif
