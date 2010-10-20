AM_CPPFLAGS = \
	-D__BUILDING_CVC4DRIVER \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

bin_PROGRAMS = cvc4

cvc4_SOURCES = \
	getopt.cpp \
	interactive_shell.h \
	interactive_shell.cpp \
	main.h \
	main.cpp \
	usage.h \
	util.cpp

cvc4_LDADD = \
	../parser/libcvc4parser.la \
	../libcvc4.la \
	../lib/libreplacements.la

if STATIC_BINARY
cvc4_LINK = $(CXXLINK) -all-static
else
cvc4_LINK = $(CXXLINK)
endif
