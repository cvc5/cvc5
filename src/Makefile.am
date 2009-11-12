INCLUDES = -I@srcdir@/include

SUBDIRS = parser sat

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_LIBADD = \
	sat/parser/libparser.a
	sat/minisat/libminisat.a

EXTRA_DIST = \
	include/assert.h \
	include/attr_type.h \
	include/command.h
	include/expr_attribute.h \
	include/expr_builder.h \
	include/expr.h \
	include/expr_manager.h \
	include/expr_value.h \
	include/kind.h \
	include/parser.h \
	include/sat.h \
	include/unique_id.h \
	include/vc.h

