INCLUDES = -I@srcdir@/../include

noinst_LIBRARIES = libparser.a

libparser_a_SOURCES = \
	pl_scanner.lpp \
	pl.ypp \
	smtlib_scanner.lpp \
	smtlib.ypp \
	parser.cpp

BUILT_SOURCES = \
	pl_scanner.cpp \
	pl.cpp \
	pl.h \
	smtlib_scanner.cpp \
	smtlib.cpp \
	smtlib.h

# produce headers too
AM_YFLAGS = -d

pl_scanner.cpp: pl_scanner.lpp
	$(LEX) $(AM_LFLAGS) $(LFLAGS) -P PL -o $@ $<
smtlib_scanner.cpp: smtlib_scanner.lpp
	$(LEX) $(AM_LFLAGS) $(LFLAGS) -P smtlib -o $@ $<

pl_scanner.o: pl.h
pl.cpp: pl.ypp
	$(YACC) $(AM_YFLAGS) $(YFLAGS) -p PL -o $@ $<


smtlib_scanner.o: smtlib.h
smtlib.cpp: smtlib.ypp
	$(YACC) $(AM_YFLAGS) $(YFLAGS) -p smtlib -o $@ $<
