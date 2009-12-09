if HAVE_CXXTESTGEN

AM_CPPFLAGS = -I. "-I$(CXXTEST)" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src"
AM_CXXFLAGS = -fno-access-control
#AM_LDFLAGS = -L@top_builddir@/src/libcvc4.la
TESTS = \
	expr/expr_black \
	expr/expr_white

lib_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/expr_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la

$(TESTS:%=%.cpp): %.cpp: %.h
	mkdir -p `dirname "$@"`
	$(CXXTESTGEN) --have-eh --have-std --error-printer -o "$@" "$<"
$(TESTS): %: %.cpp
#	get these in here somehow
#	$(TEST_CPPFLAGS) $(TEST_CXXFLAGS) $(TEST_LDFLAGS)
	$(LTCXXCOMPILE) -c -o $@.lo $<
	$(CXXLINK) $@.lo \
		@abs_top_builddir@/src/context/libcontext.la \
		@abs_top_builddir@/src/expr/libexpr.la \
		@abs_top_builddir@/src/smt/libsmt.la \
		@abs_top_builddir@/src/theory/libtheory.la \
		@abs_top_builddir@/src/util/libutil.la \
		@abs_top_builddir@/src/prop/minisat/libminisat.la

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

endif
