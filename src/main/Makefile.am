INCLUDES = -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden
AM_CPPFLAGS =

bin_PROGRAMS = cvc4

cvc4_SOURCES = \
	main.cpp \
	getopt.cpp \
	util.cpp \
	main.h \
	usage.h \
	about.h

cvc4_LDADD = \
	../parser/libcvc4parser.la \
	../libcvc4.la
