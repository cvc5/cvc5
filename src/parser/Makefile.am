# LIBCVC4PARSER_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
# LIBCVC4PARSER_RELEASE (-release) should match the CVC4 release version
#
LIBCVC4PARSER_RELEASE = @CVC4_LIBRARY_RELEASE_CODE@
LIBCVC4PARSER_VERSION = @CVC4_PARSER_LIBRARY_VERSION@

INCLUDES = -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4PARSERLIB

if USE_ANTLR
  SUBDIRS = smt
  INCLUDES += $(ANTLR_INCLUDES)
endif

lib_LTLIBRARIES = libcvc4parser.la

libcvc4parser_la_LDFLAGS = -version-info $(LIBCVC4PARSER_VERSION) -release $(LIBCVC4PARSER_RELEASE)

if USE_ANTLR
  libcvc4parser_la_LDFLAGS += $(ANTLR_LDFLAGS)
endif

libcvc4parser_la_LIBADD = \
	../libcvc4.la

libcvc4parser_la_SOURCES = \
	parser.cpp \
	parser_state.cpp \
	symbol_table.cpp \
	pl_scanner.lpp \
	pl.ypp \
	smtlib_scanner.lpp \
	smtlib.ypp

if USE_ANTLR
  libcvc4parser_la_SOURCES += \
	antlr_parser.cpp \
	antlr_parser.h
endif USE_ANTLR

BUILT_SOURCES = \
	pl_scanner.cpp \
	pl.cpp \
	pl.hpp \
	smtlib_scanner.cpp \
	smtlib.cpp \
	smtlib.hpp

# produce headers too
AM_YFLAGS = -d

pl_scanner.cpp: pl_scanner.lpp
	$(LEX) $(AM_LFLAGS) $(LFLAGS) -P PL -o $@ $<
smtlib_scanner.cpp: smtlib_scanner.lpp
	$(LEX) $(AM_LFLAGS) $(LFLAGS) -P smtlib -o $@ $<

pl_scanner.o: pl.hpp
pl.cpp: pl.ypp
	$(YACC) $(AM_YFLAGS) $(YFLAGS) -p PL -o $@ $<


smtlib_scanner.o: smtlib.hpp
smtlib.cpp: smtlib.ypp
	$(YACC) $(AM_YFLAGS) $(YFLAGS) -p smtlib -o $@ $<
