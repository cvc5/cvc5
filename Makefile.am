include $(top_srcdir)/config/doxygen.am

AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

AUTOMAKE_OPTIONS = foreign
ACLOCAL_AMFLAGS = -I config

SUBDIRS = src test contrib
DIST_SUBDIRS = $(SUBDIRS) examples

.PHONY: examples
examples: all
	(cd examples && $(MAKE) $(AM_MAKEFLAGS))

.PHONY: units systemtests regress regress0 regress1 regress2 regress3
systemtests regress regress0 regress1 regress2 regress3: all
	+(cd test && $(MAKE) $(AM_MAKEFLAGS) $@) || exit 1
# We descend into "src" with the "check" target here to ensure that
# the test prerequisites are all built.
units:
	(cd src && $(MAKE) $(AM_MAKEFLAGS) check)
	+(cd test && $(MAKE) $(AM_MAKEFLAGS) $@) || exit 1

LCOV = lcov
GENHTML = genhtml

LCOV_EXCLUDES = \
	"$(CXXTEST)/*" \
	"/usr/include/*" \
	"$(abs_top_builddir)/test/*"

.PHONY: lcov lcov-all lcov18
if COVERAGE_ENABLED

# lcov 1.7 has some bugs that we have to work around (can't do
# baseline measurement, merge between different test-names doesn't
# work...)
lcov: all
	$(LCOV) -z -d .
	(cd src && $(MAKE) $(AM_MAKEFLAGS) check)
	+(cd test/unit && $(MAKE) $(AM_MAKEFLAGS) check)
	$(LCOV) -c -d . -t cvc4_units -o cvc4-coverage-full.info
	$(LCOV) -o cvc4-coverage.info -r cvc4-coverage-full.info $(LCOV_EXCLUDES)
	mkdir -p "@top_srcdir@/html"
	$(GENHTML) -o "@top_srcdir@/html" cvc4-coverage.info
	@echo "De-mangling C++ symbols..."
	@find "@top_srcdir@/html" -name '*.func.html' | \
		xargs perl -pi -e 's#(<td class="coverFn"><a href=".*">)(.*)(</a></td>)#$$_=`c++filt "$$2"`;chomp;print "$$1<xmp>$$_</xmp>$$3\n";#e'

lcov-all: all
	$(LCOV) -z -d .
	(cd src && $(MAKE) $(AM_MAKEFLAGS) check)
	+(cd test && $(MAKE) $(AM_MAKEFLAGS) check)
	$(LCOV) -c -d . -t cvc4_units -o cvc4-coverage-full.info
	$(LCOV) -o cvc4-coverage.info -r cvc4-coverage-full.info $(LCOV_EXCLUDES)
	mkdir -p "@top_srcdir@/html"
	$(GENHTML) -o "@top_srcdir@/html" cvc4-coverage.info
	@echo "De-mangling C++ symbols..."
	@find "@top_srcdir@/html" -name '*.func.html' | \
		xargs perl -pi -e 's#(<td class="coverFn"><a href=".*">)(.*)(</a></td>)#$$_=`c++filt "$$2"`;chomp;print "$$1<xmp>$$_</xmp>$$3\n";#e'

# when we get a working lcov, we can do better stats for
# modules/test-types; unfortunately lcov 1.8 directory paths
# are broken(?) or at least different than 1.7
lcov18: all
	+@for testtype in public black white; do \
		echo; echo "=== Collecting coverage data from $$testtype unit tests ==="; \
		echo $(LCOV) -z -d .; \
		$(LCOV) -z -d . || exit 1; \
		echo "(cd src && $(MAKE) $(AM_MAKEFLAGS) check) || exit 1"; \
		(cd src && $(MAKE) $(AM_MAKEFLAGS) check) || exit 1; \
		echo "(cd test/unit && $(MAKE) $(AM_MAKEFLAGS) check TEST_SUFFIX=_$$testtype) || exit 1"; \
		(cd test/unit && $(MAKE) $(AM_MAKEFLAGS) check TEST_SUFFIX=_$$testtype) || exit 1; \
		echo $(LCOV) -c -d . -t $$testtype -o cvc4-coverage-$$testtype-full.info || exit 1; \
		$(LCOV) -c -d . -t $$testtype -o cvc4-coverage-$$testtype-full.info || exit 1; \
		echo $(LCOV) -o cvc4-coverage-$$testtype.info -r cvc4-coverage-$$testtype-full.info $(LCOV_EXCLUDES); \
		$(LCOV) -o cvc4-coverage-$$testtype.info -r cvc4-coverage-$$testtype-full.info $(LCOV_EXCLUDES) || exit 1; \
		echo; \
	done
	mkdir -p "@top_srcdir@/html"
	$(GENHTML) -o "@top_srcdir@/html" cvc4-coverage-public.info cvc4-coverage-black.info cvc4-coverage-white.info
	@echo "De-mangling C++ symbols..."
	@find "@top_srcdir@/html" -name '*.func.html' | \
		xargs perl -ni -e 's,(<td class="coverFn"><a href=".*">)(.*)(</a></td>.*),$$_=`c++filt "$$2"`;chomp;print "$$1<xmp>$$_</xmp>$$3\n";,e || print'

else

lcov lcov-all lcov18:
	@echo
	@echo "Coverage is not enabled in this build." >&2
	@echo "Please run configure with --enable-coverage." >&2
	@echo
	@false

endif

# abs_srcdir is required here to get this Makefile instead of the
# Makefile in the builddir (since $(srcdir) is stripped off of
# EXTRA_DIST files)
EXTRA_DIST = \
	Makefile.builds.in \
	Makefile.subdir \
	library_versions \
	config/build-type \
	config/mkbuilddir \
	config/doxygen.cfg \
	doc/cvc4.1_template.in \
	doc/cvc4.5.in \
	doc/libcvc4.3_template.in \
	doc/SmtEngine.3cvc4_template.in \
	doc/options.3cvc4_template.in \
	doc/libcvc4parser.3.in \
	doc/libcvc4compat.3.in
man_MANS = \
	doc/cvc4.1 \
	doc/pcvc4.1 \
	doc/cvc4.5 \
	doc/libcvc4.3 \
	doc/SmtEngine.3cvc4 \
	doc/options.3cvc4 \
	doc/libcvc4parser.3 \
	doc/libcvc4compat.3

doc/pcvc4.1:
	rm -f doc/pcvc4.1
	$(LN_S) cvc4.1 doc/pcvc4.1

dist-hook:
	cp -p "$(srcdir)/Makefile" "$(distdir)/Makefile"

distclean-local:
	test -z "$(DX_DOCDIR)" || rm -fr "$(DX_DOCDIR)"

# these have .in versions
DISTCLEANFILES = \
	doc/cvc4.1 \
	doc/cvc4.1_template \
	doc/cvc4.5 \
	doc/libcvc4.3 \
	doc/libcvc4.3_template \
	doc/libcvc4compat.3 \
	doc/libcvc4parser.3 \
	doc/SmtEngine.3cvc4 \
	doc/SmtEngine.3cvc4_template \
	doc/options.3cvc4 \
	doc/options.3cvc4_template
