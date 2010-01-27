TESTS_ENVIRONMENT =
TESTS =

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

EXTRA_DIST = \
	$(TEST_DEPS_DIST)

# rebuild tests if a library changes
$(TESTS):: $(TEST_DEPS)

# synonyms for "check"
.PHONY: regress regress0 regress1 regress2 regress3 test
regress regress0 regress1 regress2 regress3 test: check
