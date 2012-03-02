AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libcontext.la

libcontext_la_SOURCES = \
	context.cpp \
	context.h \
	context_mm.cpp \
	context_mm.h \
	cdo.h \
	cdlist.h \
	cdlist_context_memory.h \
	cdlist_forward.h \
	cdqueue.h \
	cdtrail_queue.h \
	cdhashmap.h \
	cdhashmap_forward.h \
	cdhashset.h \
	cdhashset_forward.h \
	cdcirclist.h \
	cdcirclist_forward.h \
	cdvector.h \
	stacking_map.h \
	stacking_vector.h
