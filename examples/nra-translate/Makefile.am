AM_CPPFLAGS = \
	-I@srcdir@/../../src/include -I@srcdir@/../../src -I@builddir@/../../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall

noinst_PROGRAMS = \
	smt2toqepcad \
	smt2tomathematica \
	smt2toisat \
	smt2toredlog \
	smt2todreal \
	normalize \
	smt2info	

noinst_DATA =

smt2toqepcad_SOURCES = \
	smt2toqepcad.cpp
smt2toqepcad_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

smt2tomathematica_SOURCES = \
	smt2tomathematica.cpp
smt2tomathematica_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

smt2toisat_SOURCES = \
	smt2toisat.cpp
smt2toisat_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

smt2toredlog_SOURCES = \
	smt2toredlog.cpp
smt2toredlog_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

smt2todreal_SOURCES = \
	smt2todreal.cpp
smt2todreal_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

smt2info_SOURCES = \
	smt2info.cpp
smt2info_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

normalize_SOURCES = \
	normalize.cpp
normalize_LDADD = \
	@builddir@/../../src/parser/libcvc4parser.la \
	@builddir@/../../src/libcvc4.la

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)
