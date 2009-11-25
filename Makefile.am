AM_CXXFLAGS = -Wall

AUTOMAKE_OPTIONS = foreign
ACLOCAL_AMFLAGS = -I config

SUBDIRS = src test doc contrib

.PHONY: production debug default competition
production: ; @srcdir@/configure --with-build=production && $(MAKE)
debug:      ; @srcdir@/configure --with-build=debug && $(MAKE)
default:    ; @srcdir@/configure --with-build=default && $(MAKE)
competition:; @srcdir@/configure --with-build=competition && $(MAKE)
