INCLUDES = -I@srcdir@/include -I@srcdir@

SUBDIRS = core parser sat

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_LIBADD = \
	core/libcore.a
	parser/libparser.a
	sat/minisat/libminisat.a

EXTRA_DIST = \
	include/cvc4.h \
	include/cvc4_expr.h
