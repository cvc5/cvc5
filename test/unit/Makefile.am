if HAVE_CXXTESTGEN

AM_CPPFLAGS = \
	-I. "-I@CXXTEST@" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src"
AM_CXXFLAGS_WHITE = -fno-access-control
AM_CXXFLAGS_BLACK =
AM_CXXFLAGS_PUBLIC =
AM_LDFLAGS_WHITE = \
		@abs_top_builddir@/src/context/libcontext.la \
		@abs_top_builddir@/src/expr/libexpr.la \
		@abs_top_builddir@/src/smt/libsmt.la \
		@abs_top_builddir@/src/theory/libtheory.la \
		@abs_top_builddir@/src/util/libutil.la \
		@abs_top_builddir@/src/prop/libprop.la \
		@abs_top_builddir@/src/prop/minisat/libminisat.la
AM_LDFLAGS_BLACK = \
		$(AM_LDFLAGS_WHITE)
AM_LDFLAGS_PUBLIC = \
		@abs_top_builddir@/src/libcvc4.la

TESTS = \
	expr/node_white \
	expr/node_black

# without these here, LTCXXCOMPILE, CXXLINK, etc., aren't set :-(
noinst_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la

$(TESTS:%=%.cpp): %.cpp: %.h
	mkdir -p `dirname "$@"`
	@CXXTESTGEN@ --have-eh --have-std --error-printer -o "$@" "$<"
$(filter %_white,$(TESTS)): %_white: %_white.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_WHITE) $@.lo
$(filter %_black,$(TESTS)): %_black: %_black.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_BLACK) $@.lo
$(filter %_public,$(TESTS)): %_public: %_public.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_PUBLIC) $@.lo

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

endif
