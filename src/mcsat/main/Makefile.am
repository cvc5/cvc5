AM_CPPFLAGS = \
	-D__BUILDING_CVC4DRIVER \
	-I@srcdir@/../../include -I@srcdir@/../.. -I@builddir@/../.. $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

bin_PROGRAMS = mcsat 

mcsat_SOURCES = \
	mcsat.cpp 
mcsat_LDADD = \
	@builddir@/../../parser/libcvc4parser.la \
	@builddir@/../../util/libstatistics.la \
	@builddir@/../../libcvc4.la \
	$(READLINE_LIBS)
if CVC4_NEEDS_REPLACEMENT_FUNCTIONS
mcsat_LDADD += \
	@builddir@/../lib/libreplacements.la
endif
	
EXTRA_DIST = 

SUBDIRS = 

if STATIC_BINARY
mcsat_LINK = $(CXXLINK) -all-static
else
mcsat_LINK = $(CXXLINK)
endif

