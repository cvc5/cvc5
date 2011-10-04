# LIBCVC4BINDINGS_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
LIBCVC4BINDINGS_VERSION = @CVC4_BINDINGS_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4BINDINGSLIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall

SUBDIRS = . compat

lib_LTLIBRARIES =
data_DATA =
if CVC4_LANGUAGE_BINDING_JAVA
lib_LTLIBRARIES += libcvc4bindings_java.la
data_DATA += cvc4.jar
libcvc4bindings_java_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_java_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_CSHARP
lib_LTLIBRARIES += libcvc4bindings_csharp.la
libcvc4bindings_csharp_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_csharp_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_PERL
lib_LTLIBRARIES += libcvc4bindings_perl.la
libcvc4bindings_perl_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_perl_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_PHP
lib_LTLIBRARIES += libcvc4bindings_php.la
libcvc4bindings_php_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_php_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_PYTHON
lib_LTLIBRARIES += libcvc4bindings_python.la
libcvc4bindings_python_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_python_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_OCAML
lib_LTLIBRARIES += libcvc4bindings_ocaml.la
libcvc4bindings_ocaml_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_ocaml_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_RUBY
lib_LTLIBRARIES += libcvc4bindings_ruby.la
libcvc4bindings_ruby_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_ruby_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif
if CVC4_LANGUAGE_BINDING_TCL
lib_LTLIBRARIES += libcvc4bindings_tcl.la
libcvc4bindings_tcl_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_tcl_la_LIBADD = \
	-L@builddir@/.. -lcvc4 \
	-L@builddir@/../parser -lcvc4parser
endif

nodist_libcvc4bindings_java_la_SOURCES = java.cpp
libcvc4bindings_java_la_CXXFLAGS = -fno-strict-aliasing
nodist_libcvc4bindings_csharp_la_SOURCES = csharp.cpp
nodist_libcvc4bindings_perl_la_SOURCES = perl.cpp
nodist_libcvc4bindings_php_la_SOURCES = php.cpp
nodist_libcvc4bindings_python_la_SOURCES = python.cpp
nodist_libcvc4bindings_ocaml_la_SOURCES = ocaml.cpp
nodist_libcvc4bindings_ruby_la_SOURCES = ruby.cpp
nodist_libcvc4bindings_tcl_la_SOURCES = tcl.cpp

CLEANFILES = \
	java.cpp \
	csharp.cpp \
	perl.cpp \
	php.cpp \
	python.cpp \
	ocaml.cpp \
	ruby.cpp \
	tcl.cpp

EXTRA_DIST = swig.h

MOSTLYCLEANFILES = \
        .swig_deps \
	$(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))) \
	cvc4.jar

java.lo: java.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_CPPFLAGS) -o $@ $<
cvc4.jar: java.cpp
	$(AM_V_GEN) \
	(cd java; \
	rm -fr classes; \
	mkdir -p classes; \
	$(JAVAC) -classpath . -d classes `find . -name '*.java'`; \
	cd classes); \
	$(JAR) cf $@ -C java/classes .
java.cpp:
csharp.cpp:
perl.lo: perl.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PERL_CPPFLAGS) -o $@ $<
perl.cpp:
php.lo: php.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PHP_CPPFLAGS) -Iphp -o $@ $<
php.cpp:
python.lo: python.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PYTHON_CPPFLAGS) -o $@ $<
python.cpp:
ocaml.cpp:
ruby.lo: ruby.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(RUBY_CPPFLAGS) -o $@ $<
ruby.cpp:
tcl.cpp:
java.cpp: @srcdir@/../cvc4.i
	$(AM_V_at)mkdir -p $(patsubst %.cpp,%,$@)
	$(AM_V_GEN)$(SWIG) -Wall -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -c++ -$(patsubst %.cpp,%,$@) -outdir $(patsubst %.cpp,%,$@) -package edu.nyu.acsys.CVC4 -o $@ $<
$(patsubst %,%.cpp,$(filter-out c c++ java,$(CVC4_LANGUAGE_BINDINGS))): %.cpp: @srcdir@/../cvc4.i
	$(AM_V_at)mkdir -p $(patsubst %.cpp,%,$@)
	$(AM_V_GEN)$(SWIG) -Wall -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -c++ -$(patsubst %.cpp,%,$@) -outdir $(patsubst %.cpp,%,$@) -o $@ $<

$(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))): %.d: @srcdir@/../cvc4.i
	$(AM_V_GEN)$(SWIG) -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -c++ -MM -o $(patsubst %.d,%.cpp,$@) $<
# .PHONY so they get rebuilt each time
.PHONY: .swig_deps $(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
.swig_deps: $(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
	$(AM_V_GEN)cat $+ </dev/null >$@
@mk_include@ .swig_deps

clean-local:; rm -fr $(patsubst %.cpp,%,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
