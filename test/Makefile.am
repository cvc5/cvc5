if HAVE_CXXTESTGEN

AM_CPPFLAGS = -I. "-I$(CXXTEST)" "-I@top_srcdir@/src/include" "-I@top_srcdir@/src"
AM_CXXFLAGS = -fno-access-control
AM_LDFLAGS = -L@top_builddir@/src/libcvc4.a
TESTS = \
	expr/expr_black \
	expr/expr_white

%.cpp: %.h
	$(CXXTESTGEN) --have-eh --have-std --error-printer -o $@ $<
%: %.cpp
	$(CXX) $(TEST_CPPFLAGS) $(AM_CPPFLAGS) $(TEST_CXXFLAGS) $(AM_CXXFLAGS) -o $@ $(TEST_LDFLAGS) $(AM_LDFLAGS) $< @top_builddir@/src/libcvc4.a

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

endif

