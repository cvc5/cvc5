INCLUDES = -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -fvisibility=hidden

bin_PROGRAMS = cvc4

cvc4_SOURCES = \
	main.cpp \
	getopt.cpp \
	util.cpp

cvc4_LDADD = \
	../parser/libparser.la \
	../libcvc4.la
