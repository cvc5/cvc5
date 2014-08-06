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

AUTOMAKE_OPTIONS = subdir-objects

AM_CPPFLAGS = \
	-D__BUILDING_CVC4BINDINGSLIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall

SUBDIRS = compat

# any binding-specific flags to pass to swig
java_cpp_SWIGFLAGS = -package edu.nyu.acsys.CVC4

lib_LTLIBRARIES =
bin_PROGRAMS =
javadatadir = $(datadir)/java
javalibdir = $(libdir)/jni
ocamldatadir = $(libdir)/ocaml/cvc4
ocamllibdir = $(libdir)/ocaml/cvc4
perldatadir = $(datadir)/perl5
perllibdir = $(libdir)/perl5
phpdatadir = $(datadir)/php
phplibdir = $(libdir)/php
pythondatadir = $(datadir)/pyshared
pythonlibdir = $(libdir)/pyshared
csharpdatadir = $(datadir)/csharp
csharplibdir = $(libdir)/csharp
rubylibdir = $(libdir)/ruby
tcllibdir = $(libdir)/tcltk
javadata_DATA =
javalib_LTLIBRARIES=
ocamldata_DATA =
ocamllib_LTLIBRARIES=
perldata_DATA =
perllib_LTLIBRARIES =
phpdata_DATA =
phplib_LTLIBRARIES =
pythondata_DATA =
pythonlib_LTLIBRARIES =
csharpdata_DATA =
csharplib_LTLIBRARIES =
rubylib_LTLIBRARIES =
tcllib_LTLIBRARIES =
if CVC4_HAS_SWIG
if CVC4_LANGUAGE_BINDING_JAVA 
javalib_LTLIBRARIES += java/libcvc4jni.la
javadata_DATA += CVC4.jar
java_libcvc4jni_la_LDFLAGS = \
	-module \
	-shrext $(CVC4_JAVA_MODULE_EXT) \
	-version-info $(LIBCVC4BINDINGS_VERSION)
java_libcvc4jni_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
endif
if CVC4_LANGUAGE_BINDING_CSHARP
csharplib_LTLIBRARIES += csharp/CVC4.la
csharp_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
csharp_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
endif
if CVC4_LANGUAGE_BINDING_PERL
perllib_LTLIBRARIES += perl/CVC4.la
perl_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
perl_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
perldata_DATA += perl/CVC4.pm
endif
if CVC4_LANGUAGE_BINDING_PHP
phplib_LTLIBRARIES += php/CVC4.la
php_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
php_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
phpdata_DATA += php/CVC4.php
endif
if CVC4_LANGUAGE_BINDING_PYTHON
pythonlib_LTLIBRARIES += python/CVC4.la
python_CVC4_la_CXXFLAGS = $(PYTHON_CXXFLAGS)
python_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
python_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
pythondata_DATA += python/CVC4.py
endif
if CVC4_LANGUAGE_BINDING_OCAML
ocamllib_LTLIBRARIES += ocaml/CVC4.la
bin_PROGRAMS += cvc4_ocaml_top
# We provide a make rule below, but we have to tell automake to lay off, too,
# otherwise it tries (and fails) to package the nonexistent cvc4_ocaml_top.c!
cvc4_ocaml_top_SOURCES =
ocamldata_DATA += ocaml/swig.cmo ocaml/swig.cmi ocaml/swigp4.cmo ocaml/swigp4.cmi ocaml/CVC4.cmo ocaml/CVC4.cmi
ocaml_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
ocaml_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
endif
if CVC4_LANGUAGE_BINDING_RUBY
rubylib_LTLIBRARIES += ruby/CVC4.la
ruby_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
ruby_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
endif
if CVC4_LANGUAGE_BINDING_TCL
tcllib_LTLIBRARIES += tcl/CVC4.la
tcl_CVC4_la_LDFLAGS = \
	-module \
	-version-info $(LIBCVC4BINDINGS_VERSION)
tcl_CVC4_la_LIBADD = \
	@builddir@/../libcvc4.la \
	@builddir@/../parser/libcvc4parser.la
endif
# this endif matches the "if CVC4_HAS_SWIG" above
endif

nodist_java_libcvc4jni_la_SOURCES = java.cpp
java_libcvc4jni_la_CXXFLAGS = -Wno-all @FNO_STRICT_ALIASING@ @WNO_UNUSED_VARIABLE@ @WNO_UNINITIALIZED@
nodist_csharp_CVC4_la_SOURCES = csharp.cpp
nodist_perl_CVC4_la_SOURCES = perl.cpp
nodist_php_CVC4_la_SOURCES = php.cpp
nodist_python_CVC4_la_SOURCES = python.cpp
nodist_ocaml_CVC4_la_SOURCES = ocaml.cpp
nodist_ruby_CVC4_la_SOURCES = ruby.cpp
nodist_tcl_CVC4_la_SOURCES = tcl.cpp

CLEANFILES = \
	java.cpp \
	csharp.cpp \
	perl.cpp \
	php.cpp \
	python.cpp \
	ocaml.cpp \
	ruby.cpp \
	tcl.cpp

EXTRA_DIST = \
	swig.h \
	java_iterator_adapter.h \
	java_stream_adapters.h

MOSTLYCLEANFILES = \
        .swig_deps \
	$(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))) \
	CVC4.jar

java_libcvc4jni_la-java.lo: java.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_CPPFLAGS) $(java_libcvc4jni_la_CXXFLAGS) -o $@ $<
java.lo: java.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_CPPFLAGS) $(java_libcvc4jni_la_CXXFLAGS) -o $@ $<
CVC4.jar: java.cpp
	$(AM_V_GEN) \
	(cd java && \
	rm -fr classes && \
	mkdir -p classes && \
	$(JAVAC) -source 1.5 -target 1.5 -classpath . -d classes `find . -name '*.java'` && \
	cd classes) && \
	$(JAR) cf $@ -C java/classes .
#java.cpp:;
csharp.lo: csharp.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(CSHARP_CPPFLAGS) -o $@ $<
#csharp.cpp:;
perl.lo: perl.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PERL_CPPFLAGS) -o $@ $<
#perl.cpp:;
perl/CVC4.pm: perl.cpp
php.lo: php.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(PHP_CPPFLAGS) -Iphp -o $@ $<
#php.cpp:;
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
#ocaml.cpp:;
cvc4_ocaml_top$(EXEEXT): ocaml/CVC4.la ocaml/swig.cmo ocaml/swig.cmi ocaml/swigp4.cmo ocaml/CVC4.cmo ocaml/CVC4.cmi
	$(AM_V_GEN)\
	$(OCAMLFIND) ocamlmktop -I $(ocamldatadir) -custom -o cvc4_ocaml_top$(EXEEXT) -package camlp4 dynlink.cma camlp4o.cma ocaml/swig.cmo ocaml/swigp4.cmo ocaml/CVC4.cmo -cclib ocaml/.libs/CVC4.so -cclib -lstdc++
ruby.lo: ruby.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(RUBY_CPPFLAGS) -o $@ $<
tcl.lo: tcl.cpp
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(TCL_CPPFLAGS) -o $@ $<
#tcl.cpp:;

if CVC4_HAS_SWIG

$(patsubst %,%.cpp,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))): %.cpp: @srcdir@/../cvc4.i
	$(AM_V_at)mkdir -p $(patsubst %.cpp,%,$@)
	$(AM_V_GEN)$(SWIG) -Wall -I@builddir@/.. -I@srcdir@/../include -I@srcdir@/.. -c++ -$(patsubst %.cpp,%,$@) -outdir $(patsubst %.cpp,%,$@) $($(subst .,_,$@)_SWIGFLAGS) -o $@ $<

$(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))): %.d: @srcdir@/../cvc4.i
	$(AM_V_GEN)$(SWIG) -I@builddir@/.. -I@srcdir@/../include -I@srcdir@/.. -c++ -$(patsubst %.d,%,$@) -MM -o $(patsubst %.d,%.cpp,$@) $<
# .PHONY so they get rebuilt each time
.PHONY: .swig_deps $(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
.swig_deps: $(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
	$(AM_V_GEN)cat $+ </dev/null >$@
@mk_include@ .swig_deps

endif

clean-local:; rm -fr $(patsubst %.cpp,%,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
