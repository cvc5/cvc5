SUBDIRS = nra-translate sets-translate hashsmt api .

AM_CPPFLAGS = \
	-I@srcdir@/../src/include -I@srcdir@/../src -I@builddir@/../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall


noinst_PROGRAMS = \
	simple_vc_cxx \
	translator

noinst_DATA =

if CVC4_LANGUAGE_BINDING_JAVA
noinst_DATA += \
	SimpleVC.class
endif


simple_vc_cxx_SOURCES = \
	simple_vc_cxx.cpp
simple_vc_cxx_LDADD = \
	@builddir@/../src/parser/libcvc4parser.la \
	@builddir@/../src/libcvc4.la

translator_SOURCES = \
	translator.cpp
translator_LDADD = \
	@builddir@/../src/parser/libcvc4parser.la \
	@builddir@/../src/libcvc4.la

SimpleVC.class: SimpleVC.java
	$(AM_V_JAVAC)$(JAVAC) -classpath "@builddir@/../src/bindings/CVC4.jar" -d "@builddir@" $<

EXTRA_DIST = \
	SimpleVC.java \
	SimpleVC.ml \
	SimpleVC.php \
	SimpleVC.pl \
	SimpleVC.py \
	SimpleVC.rb \
	SimpleVC.tcl \
	README

if STATIC_BINARY
simple_vc_cxx_LINK = $(CXXLINK) -all-static
else
simple_vc_cxx_LINK = $(CXXLINK)
endif

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)

MOSTLYCLEANFILES = $(noinst_DATA)

# for silent automake rules
AM_V_JAVAC = $(am__v_JAVAC_$(V))
am__v_JAVAC_ = $(am__v_JAVAC_$(AM_DEFAULT_VERBOSITY))
am__v_JAVAC_0 = @echo "  JAVAC " $@;
