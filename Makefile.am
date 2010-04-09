include $(top_srcdir)/config/doxygen.am

AM_CXXFLAGS = -Wall

AUTOMAKE_OPTIONS = foreign
ACLOCAL_AMFLAGS = -I config

SUBDIRS = src test contrib

.PHONY: regress0 regress1 regress2 regress3
regress0 regress1 regress2 regress3: all
	(cd test && $(MAKE) $(AM_MAKEFLAGS) $@) || exit 1

LCOV = lcov
GENHTML = genhtml

LCOV_EXCLUDES = \
	"$(CXXTEST)/*" \
	"/usr/include/*" \
	"$(abs_top_builddir)/test/*"

# lcov 1.7 has some bugs that we have to work around (can't do
# baseline measurement, merge between different test-names doesn't
# work...)
.PHONY: lcov
lcov: all
	$(LCOV) -z -d .
	$(MAKE) check -C test/unit
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
.PHONY: lcov18
lcov18: all
	@for testtype in public black white; do \
		echo; echo "=== Collecting coverage data from $$testtype unit tests ==="; \
		echo $(LCOV) -z -d .; \
		$(LCOV) -z -d . || exit 1; \
		echo $(MAKE) check -C test/unit TEST_SUFFIX=_$$testtype || exit 1; \
		$(MAKE) check -C test/unit TEST_SUFFIX=_$$testtype || exit 1; \
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
		xargs perl -pi -e 's,(<td class="coverFn"><a href=".*">)(.*)(</a></td>),$$_=`c++filt "$$2"`;chomp;print "$$1<xmp>$$_</xmp>$$3";,e'
