AM_CPPFLAGS = \
	-D__BUILDING_CVC4BINDINGSLIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

lib_LTLIBRARIES =
data_DATA =
if CVC4_LANGUAGE_BINDING_JAVA
lib_LTLIBRARIES += libcvc4bindings_java.la
data_DATA += cvc4.jar
endif
#	cvc4bindings_csharp.so \
#	cvc4bindings_perl.so \
#	cvc4bindings_php.so \
#	cvc4bindings_python.so \
#	cvc4bindings_ocaml.so \
#	cvc4bindings_ruby.so \
#	cvc4bindings_tcl.so

nodist_libcvc4bindings_java_la_SOURCES = java.cpp
#nodist_cvc4bindings_csharp_so_SOURCES = csharp.cpp
#nodist_cvc4bindings_perl_so_SOURCES = perl.cpp
#nodist_cvc4bindings_php_so_SOURCES = php.cpp
#nodist_cvc4bindings_python_so_SOURCES = python.cpp
#nodist_cvc4bindings_ocaml_so_SOURCES = ocaml.cpp
#nodist_cvc4bindings_ruby_so_SOURCES = ruby.cpp
#nodist_cvc4bindings_tcl_so_SOURCES = tcl.cpp

BUILT_SOURCES = \
	java.cpp \
	csharp.cpp \
	perl.cpp \
	php.cpp \
	python.cpp \
	ocaml.cpp \
	ruby.cpp \
	tcl.cpp

CLEANFILES = \
	$(BUILT_SOURCES) \
        .swig_deps \
	$(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))) \
	cvc4.jar

java.lo: java.cpp; $(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_INCLUDES) -o $@ $<
cvc4.jar: java.cpp; $(AM_V_GEN)jar cf $@ -C java .
java.cpp:
csharp.cpp:
perl.cpp:
php.cpp:
python.cpp:
ocaml.cpp:
ruby.cpp:
tcl.cpp:
$(patsubst %,%.cpp,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))): %.cpp: @srcdir@/../cvc4.i
	$(AM_V_at)mkdir -p $(patsubst %.cpp,%,$@)
	$(AM_V_GEN)$(SWIG) -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -module cvc4 -c++ -$(patsubst %.cpp,%,$@) -outdir $(patsubst %.cpp,%,$@) -package edu.nyu.acsys -o $@ $<

$(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))): %.d: @srcdir@/../cvc4.i
	$(AM_V_GEN)$(SWIG) -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -module cvc4 -c++ -MM -o $(patsubst %.d,%.cpp,$@) $<
# .PHONY so they get rebuilt each time
.PHONY: .swig_deps $(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
.swig_deps: $(patsubst %,%.d,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
	$(AM_V_GEN)cat $+ </dev/null >$@
@mk_include@ .swig_deps

clean-local:; rm -fr $(patsubst %.cpp,%,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS)))
