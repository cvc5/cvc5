AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libcontext.la

libcontext_la_SOURCES = \
	context.cpp \
	context.h \
	context_mm.cpp \
	context_mm.h \
	cdo.h \
	cdlist.h \
	cdchunk_list.h \
	cdlist_forward.h \
	cdqueue.h \
	cdtrail_queue.h \
	cdtrail_hashmap.h \
	cdtrail_hashmap_forward.h \
	cdinsert_hashmap.h \
	cdinsert_hashmap_forward.h \
	cdhashmap.h \
	cdhashmap_forward.h \
	cdhashset.h \
	cdhashset_forward.h \
	cdvector.h \
	cdmaybe.h \
	stacking_map.h \
	stacking_vector.h \
	cddense_set.h
