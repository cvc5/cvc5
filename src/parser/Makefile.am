INCLUDES = -I@srcdir@/../include -I@srcdir@/.. -I@builddir@
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS = -D__BUILDING_CVC4LIB

nobase_lib_LTLIBRARIES = libcvc4parser.la

libcvc4parser_la_SOURCES = \
	parser.cpp \
	parser_state.cpp \
	symbol_table.cpp \
	pl_scanner.lpp \
	pl.ypp \
	smtlib_scanner.lpp \
	smtlib.ypp

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
