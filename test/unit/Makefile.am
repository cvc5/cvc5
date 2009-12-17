# all unit tests
UNIT_TESTS = \
	expr/node_white \
	expr/node_black \
	parser/cvc/cvc_parser_black \
	parser/smt/smt_parser_black

# things that aren't tests but that tests rely on and need to
# go into the distribution
TEST_DEPS =

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
	$(TEST_DEPS)

# without these here, LTCXXCOMPILE, CXXLINK, etc., aren't set :-(
noinst_LTLIBRARIES = libdummy.la
libdummy_la_SOURCES = expr/node_black.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la

$(TESTS:%=%.cpp): %.cpp: %.h
	mkdir -p `dirname "$@"`
	@CXXTESTGEN@ --have-eh --have-std --error-printer -o "$@" "$<"
$(filter %_white,$(TESTS)): %_white: %_white.cpp
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_WHITE) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_WHITE) $@.lo
$(filter %_black,$(TESTS)): %_black: %_black.cpp
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_BLACK) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_BLACK) $@.lo
$(filter %_public,$(TESTS)): %_public: %_public.cpp
	$(LTCXXCOMPILE) $(AM_CXXFLAGS_PUBLIC) -c -o $@.lo $<
	$(CXXLINK) $(AM_LDFLAGS_PUBLIC) $@.lo

MOSTLYCLEANFILES = $(TESTS) $(TESTS:%=%.cpp)

else

# force a user-visible failure for "make check"
TESTS = no_cxxtest

EXTRA_DIST = \
	$(UNIT_TESTS) \
	$(TEST_DEPS)

endif
