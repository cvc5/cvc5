AM_CPPFLAGS = \
	-D__BUILDING_CVC4DRIVER \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

bin_PROGRAMS = cvc4
noinst_LIBRARIES = libmain.a

libmain_a_SOURCES = \
	interactive_shell.h \
	interactive_shell.cpp \
	main.h \
	main.cpp \
	usage.h \
	util.cpp

cvc4_SOURCES =
cvc4_LDADD = \
	libmain.a \
	../parser/libcvc4parser.la \
	../libcvc4.la \
	../lib/libreplacements.la \
	$(READLINE_LDFLAGS)

BUILT_SOURCES = \
	$(TOKENS_FILES)

TOKENS_FILES = \
	cvc_tokens.h \
	smt_tokens.h \
	smt2_tokens.h

cvc_tokens.h: @srcdir@/../parser/cvc/Cvc.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9][a-zA-Z0-9]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9]\+\)'\''.*/"\1",/' | sort -u >$@
smt_tokens.h: @srcdir@/../parser/smt/Smt.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9][a-zA-Z0-9]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9]\+\)'\''.*/"\1",/' | sort -u >$@
smt2_tokens.h: @srcdir@/../parser/smt2/Smt2.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9][a-zA-Z0-9]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9]\+\)'\''.*/"\1",/' | sort -u >$@

clean-local:
	rm -f $(BUILT_SOURCES)

if STATIC_BINARY
cvc4_LINK = $(CXXLINK) -all-static
else
cvc4_LINK = $(CXXLINK)
endif
