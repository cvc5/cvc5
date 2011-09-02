AM_CPPFLAGS = \
	-D__BUILDING_CVC4BINDINGSLIB \
	-I@srcdir@/../include -I@srcdir@/.. -I@builddir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

lib_LTLIBRARIES =
if CVC4_LANGUAGE_BINDING_JAVA
lib_LTLIBRARIES += libcvc4bindings_java.la
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
	cvc4.java \
	cvc4.cs \
	cvc4JNI.java \
	cvc4.php \
	cvc4PINVOKE.cs \
	cvc4.pm \
	cvc4.py \
	php_cvc4.h

java.lo: java.cpp; $(LTCXXCOMPILE) $(JAVA_INCLUDES) -o $@ $<
java.cpp::
csharp.cpp::
perl.cpp::
php.cpp::
python.cpp::
ocaml.cpp::
ruby.cpp::
tcl.cpp::
$(patsubst %,%.cpp,$(filter-out c c++,$(CVC4_LANGUAGE_BINDINGS))):: %.cpp: @srcdir@/../smt/smt_engine.h
	$(AM_V_GEN)$(SWIG) -w503 -I@srcdir@/../include -I@srcdir@/.. -I@builddir@/.. -module cvc4 -c++ -$(patsubst %.cpp,%,$@) -o $@ $<
