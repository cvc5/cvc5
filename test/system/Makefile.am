TESTS_ENVIRONMENT =
TEST_EXTENSIONS = .class
CPLUSPLUS_TESTS = \
	boilerplate \
	ouroborous \
	two_smt_engines \
	smt2_compliance \
	statistics

if CVC4_BUILD_LIBCOMPAT
#CPLUSPLUS_TESTS += \
#	cvc3_main
endif

TESTS = $(CPLUSPLUS_TESTS)

if CVC4_LANGUAGE_BINDING_JAVA
TESTS += CVC4JavaTest.class
endif

# we set the DYLD_LIBRARY_PATH in addition to -Djava.library.path, seems
# to be necessary on Mac
CLASS_LOG_COMPILER = env DYLD_LIBRARY_PATH=$(abs_top_builddir)/src/bindings/java/.libs:$(abs_top_builddir)/src/.libs:$(abs_top_builddir)/src/parser/.libs @srcdir@/run_java_test $(JAVA) -classpath .:@abs_top_builddir@/src/bindings/CVC4.jar -Djava.library.path=$(abs_top_builddir)/src/bindings/java/.libs:$(abs_top_builddir)/src/.libs:$(abs_top_builddir)/src/parser/.libs

# Things that aren't tests but that tests rely on and need to
# go into the distribution
TEST_DEPS_DIST = \
	cvc3_main.cpp \
	cvc3_george.h \
	CVC4JavaTest.java \
	run_java_test
#	cvc3_george.cpp

# Make-level dependencies; these don't go in the source distribution
# but should trigger a re-compile of all unit tests.  Libraries are
# included here because (1) if static-linking, the tests must be
# relinked, and (2) if they've changed that means the sources changed,
# and that means we should ensure the tests compile against any
# changes made in the header files.
TEST_DEPS_NODIST = \
	$(abs_top_builddir)/src/libcvc4.la \
	$(abs_top_builddir)/src/parser/libcvc4parser.la

if CVC4_BUILD_LIBCOMPAT
TEST_DEPS_NODIST += \
	$(abs_top_builddir)/src/compat/libcvc4compat.la
#	cvc3_george.lo
endif

TEST_DEPS = \
	$(TEST_DEPS_DIST) \
	$(TEST_DEPS_NODIST)

EXTRA_DIST = \
	$(CPLUSPLUS_TESTS:%=%.cpp) \
	$(TEST_DEPS_DIST)

MOSTLYCLEANFILES = $(TESTS)

if STATIC_BINARY
system_LINK = $(CXXLINK) -all-static
else
system_LINK = $(CXXLINK)
endif

AM_CPPFLAGS = \
	-I. \
	"-I@top_builddir@/src" \
	"-I@top_srcdir@/src/include" \
	"-I@top_srcdir@/lib" \
	"-I@top_srcdir@/src" \
	"-I@top_srcdir@/src/prop/minisat" \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-D __BUILDING_CVC4_SYSTEM_TEST \
	$(TEST_CPPFLAGS)

LIBADD =
if CVC4_BUILD_LIBCOMPAT
LIBADD += \
	@abs_top_builddir@/src/compat/libcvc4compat.la
endif
LIBADD += \
	@abs_top_builddir@/src/parser/libcvc4parser.la \
	@abs_top_builddir@/src/libcvc4.la

# WHEN SYSTEM TESTS ARE ADDED, BUILD LIKE THIS:
$(filter-out %.class.lo,$(TESTS:%=%.lo)): %.lo: %.cpp $(LIBADD)
	$(AM_V_CXX)$(LTCXXCOMPILE) $(AM_CXXFLAGS) -c -o $@ $<
$(filter-out %.class,$(TESTS)): %: %.lo $(LIBADD)
	$(AM_V_CXXLD)$(system_LINK) $(LIBADD) $(AM_LDFLAGS) $(LIBS) $<
CVC4JavaTest.class: CVC4JavaTest.java @abs_top_builddir@/src/bindings/CVC4.jar @abs_top_builddir@/src/bindings/java/libcvc4jni.la
	$(AM_V_JAVAC)$(JAVAC) -classpath @abs_top_builddir@/src/bindings/CVC4.jar -d $(builddir) $<

# for silent automake rules
AM_V_JAVAC = $(am__v_JAVAC_$(V))
am__v_JAVAC_ = $(am__v_JAVAC_$(AM_DEFAULT_VERBOSITY))
am__v_JAVAC_0 = @echo "  JAVAC " $@;

# trick automake into setting LTCXXCOMPILE, CXXLINK, etc.
if CVC4_FALSE
noinst_LTLIBRARIES = libdummy.la
nodist_libdummy_la_SOURCES = ouroborous.cpp
libdummy_la_LIBADD = @abs_top_builddir@/src/libcvc4.la
endif

# rebuild tests if a library changes
#$(TESTS):: $(TEST_DEPS)

MAKEFLAGS = -k
export VERBOSE = 1

# synonyms for "check" in this directory in this directory
.PHONY: test systemtests
test systemtests: check

# no-ops here
.PHONY: units regress regress0 regress1 regress2 regress3 regress4
units regress regress0 regress1 regress2 regress3 regress4:
