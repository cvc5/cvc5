AM_CXXFLAGS = -Wall

AUTOMAKE_OPTIONS = foreign
ACLOCAL_AMFLAGS = -I config

SUBDIRS = src test doc contrib

@mk_include@ @top_srcdir@/Makefile.reconf_args

.PHONY: production debug default competition
production debug default competition:
	cd @top_srcdir@; \
	dir="builds/`config/config.guess`/`config/build-type $@ $(BTARGS)`"; \
	if test -e "$$dir"; then \
		cd "$$dir" && $(MAKE); \
	else \
		./configure --with-build=$@ $(CONFARGS) && $(MAKE); \
	fi

.PHONY: regress0 regress1 regress2 regress3
regress0 regress1 regress2 regress3:
	(cd test && $(MAKE) $(AM_MAKEFLAGS) $@) || exit 1
