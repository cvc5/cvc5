AM_CXXFLAGS = -Wall

AUTOMAKE_OPTIONS = foreign
ACLOCAL_AMFLAGS = -I config

SUBDIRS = src test doc contrib

.PHONY: regress0 regress1 regress2 regress3
regress0 regress1 regress2 regress3:
	(cd test && $(MAKE) $(AM_MAKEFLAGS) $@) || exit 1
