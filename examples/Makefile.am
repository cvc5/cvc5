SUBDIRS = nra-translate sets-translate hashsmt api .

AM_CPPFLAGS = \
	-I@srcdir@/../src/include -I@srcdir@/../src -I@builddir@/../src $(ANTLR_INCLUDES)
AM_CXXFLAGS = -Wall
AM_CFLAGS = -Wall


noinst_PROGRAMS = \
	simple_vc_cxx \
	translator


if CVC4_BUILD_LIBCOMPAT
noinst_PROGRAMS += \
	simple_vc_compat_cxx
if CVC4_LANGUAGE_BINDING_C
noinst_PROGRAMS += \
	simple_vc_compat_c
endif
endif

noinst_DATA =

if CVC4_LANGUAGE_BINDING_JAVA
noinst_DATA += \
	SimpleVC.class
if CVC4_BUILD_LIBCOMPAT
noinst_DATA += \
	SimpleVCCompat.class
endif
endif


simple_vc_cxx_SOURCES = \
	simple_vc_cxx.cpp
simple_vc_cxx_LDADD = \
	@builddir@/../src/parser/libcvc4parser.la \
	@builddir@/../src/libcvc4.la

simple_vc_compat_cxx_SOURCES = \
	simple_vc_compat_cxx.cpp
simple_vc_compat_cxx_LDADD = \
	@builddir@/../src/compat/libcvc4compat.la \
	@builddir@/../src/parser/libcvc4parser.la \
	@builddir@/../src/libcvc4.la

simple_vc_compat_c_SOURCES = \
	simple_vc_compat_c.c
simple_vc_compat_c_LDADD = \
	@builddir@/../src/bindings/compat/c/libcvc4bindings_c_compat.la

translator_SOURCES = \
	translator.cpp
translator_LDADD = \
	@builddir@/../src/parser/libcvc4parser.la \
	@builddir@/../src/libcvc4.la

SimpleVC.class: SimpleVC.java
	$(AM_V_JAVAC)$(JAVAC) -classpath "@builddir@/../src/bindings/CVC4.jar" -d "@builddir@" $<
SimpleVCCompat.class: SimpleVCCompat.java
	$(AM_V_JAVAC)$(JAVAC) -classpath "@builddir@/../src/bindings/compat/java/CVC4compat.jar" -d "@builddir@" $<

EXTRA_DIST = \
	SimpleVC.java \
	SimpleVCCompat.java \
	SimpleVC.ml \
	SimpleVC.php \
	SimpleVC.pl \
	SimpleVC.py \
	SimpleVC.rb \
	SimpleVC.tcl \
	README

if STATIC_BINARY
simple_vc_cxx_LINK = $(CXXLINK) -all-static
simple_vc_compat_cxx_LINK = $(CXXLINK) -all-static
simple_vc_compat_c_LINK = $(LINK) -all-static
else
simple_vc_cxx_LINK = $(CXXLINK)
simple_vc_compat_cxx_LINK = $(CXXLINK)
simple_vc_compat_c_LINK = $(LINK)
endif

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)

MOSTLYCLEANFILES = $(noinst_DATA)

# for silent automake rules
AM_V_JAVAC = $(am__v_JAVAC_$(V))
am__v_JAVAC_ = $(am__v_JAVAC_$(AM_DEFAULT_VERBOSITY))
am__v_JAVAC_0 = @echo "  JAVAC " $@;

