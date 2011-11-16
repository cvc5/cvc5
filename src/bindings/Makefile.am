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
bin_PROGRAMS =
javadatadir = $(datadir)/java
ocamldatadir = $(libdir)/ocaml/cvc4
javadata_DATA =
ocamldata_DATA =
if CVC4_LANGUAGE_BINDING_JAVA
lib_LTLIBRARIES += libcvc4bindings_java.la
javadata_DATA += cvc4.jar
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
bin_PROGRAMS += cvc4_ocaml_top
# We provide a make rule below, but we have to tell automake to lay off, too,
# otherwise it tries (and fails) to package the nonexistent cvc4_ocaml_top.c!
cvc4_ocaml_top_SOURCES =
ocamldata_DATA += ocaml/swig.cmo ocaml/swig.cmi ocaml/swigp4.cmo ocaml/swigp4.cmi ocaml/CVC4.cmo ocaml/CVC4.cmi
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

libcvc4bindings_java_la-java.lo java.lo: java.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_CPPFLAGS) -o $@ $<
cvc4.jar: java.cpp
	$(AM_V_GEN) \
	(cd java; \
	rm -fr classes; \
	mkdir -p classes; \
	$(JAVAC) -classpath . -d classes `find . -name '*.java'`; \
	cd classes); \
	$(JAR) cf $@ -C java/classes .
java.cpp:;
csharp.lo: csharp.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(CSHARP_CPPFLAGS) -o $@ $<
csharp.cpp:;
perl.lo: perl.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PERL_CPPFLAGS) -o $@ $<
perl.cpp:;
php.lo: php.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PHP_CPPFLAGS) -Iphp -o $@ $<
php.cpp:;
python.lo: python.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PYTHON_CPPFLAGS) -o $@ $<
ocaml.lo: ocaml.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(OCAML_CPPFLAGS) -o $@ $<
ocaml/swig.cmo: ocaml/swig.ml ocaml/swig.cmi; $(AM_V_GEN)$(OCAMLC) -I ocaml -c -o $@ $<
ocaml/swig.cmi: ocaml/swig.mli; $(AM_V_GEN)$(OCAMLC) -I ocaml -c -o $@ $<
ocaml/CVC4.cmo: ocaml/CVC4.ml ocaml/CVC4.cmi; $(AM_V_GEN)$(OCAMLC) -I ocaml -c -o $@ $<
ocaml/CVC4.cmi: ocaml/CVC4.mli; $(AM_V_GEN)$(OCAMLC) -I ocaml -c -o $@ $<
ocaml/swigp4.cmo: ocaml/swigp4.ml; $(AM_V_GEN)$(OCAMLFIND) ocamlc -package camlp4 -pp "$(CAMLP4O) pa_extend.cmo q_MLast.cmo" -o $@ -c $<
ocaml/swig.ml:; $(AM_V_GEN)cd ocaml && $(SWIG) -ocaml -co swig.ml
ocaml/swig.mli:; $(AM_V_GEN)cd ocaml && $(SWIG) -ocaml -co swig.mli
ocaml/swigp4.ml:; $(AM_V_GEN)cd ocaml && $(SWIG) -ocaml -co swigp4.ml
ocaml.cpp:;
cvc4_ocaml_top: libcvc4bindings_ocaml.la ocaml/swig.cmo ocaml/swig.cmi ocaml/swigp4.cmo ocaml/CVC4.cmo ocaml/CVC4.cmi libcvc4bindings_ocaml.la
	$(AM_V_GEN)\
	$(OCAMLFIND) ocamlmktop -I $(ocamldatadir) -custom -o cvc4_ocaml_top -package camlp4 dynlink.cma camlp4o.cma ocaml/swig.cmo ocaml/swigp4.cmo ocaml/CVC4.cmo -cclib -L.libs -cclib -L. -cclib -lcvc4bindings_ocaml -cclib -lstdc++
ruby.lo: ruby.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(RUBY_CPPFLAGS) -o $@ $<
tcl.lo: tcl.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(TCL_CPPFLAGS) -o $@ $<
tcl.cpp:;
java.cpp: @srcdir@/../cvc4.i
	$(AM_V_at)mkdir -p $(patsubst %.cpp,%,$@)
	$(AM_V_GEN)$(SWIG) -Wall -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -c++ -$(patsubst %.cpp,%,$@) -outdir $(patsubst %.cpp,%,$@) -package edu.nyu.acsys.CVC4 -o $@ $<
# somehow, NULL gets translated to ((void*)0) prematurely, and this causes compiler errors ?!
ruby.cpp python.cpp: @srcdir@/../cvc4.i
	$(AM_V_at)mkdir -p $(patsubst %.cpp,%,$@)
	$(AM_V_GEN)$(SWIG) -Wall -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -c++ -$(patsubst %.cpp,%,$@) -outdir $(patsubst %.cpp,%,$@) -o $@ $<
	$(AM_V_at)mv $@ $@.old && sed 's,((void\*) 0),NULL,g' $@.old > $@
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
