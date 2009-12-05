AM_CXXFLAGS = -Wall

AUTOMAKE_OPTIONS = foreign
ACLOCAL_AMFLAGS = -I config

SUBDIRS = src test doc contrib

.PHONY: production debug default competition
production: ; (cd @top_srcdir@ && ./configure --with-build=production && $(MAKE))
debug:      ; (cd @top_srcdir@ && ./configure --with-build=debug && $(MAKE))
default:    ; (cd @top_srcdir@ && ./configure --with-build=default && $(MAKE))
competition:; (cd @top_srcdir@ && ./configure --with-build=competition && $(MAKE))
