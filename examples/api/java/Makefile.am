noinst_DATA =

if CVC4_LANGUAGE_BINDING_JAVA
noinst_DATA += \
	CVC4Streams.class \
	BitVectors.class \
	BitVectorsAndArrays.class \
	Combination.class \
	HelloWorld.class \
	LinearArith.class \
	Datatypes.class \
	PipedInput.class \
	Strings.class
endif

%.class: %.java
	$(AM_V_JAVAC)$(JAVAC) -classpath "@builddir@/../../../src/bindings/CVC4.jar" -d "@builddir@" $<

EXTRA_DIST = \
	CVC4Streams.java \
	BitVectors.java \
	BitVectorsAndArrays.java \
	Combination.java \
	HelloWorld.java \
	LinearArith.java \
	Datatypes.java \
	PipedInput.java \
	Strings.java

# for installation
examplesdir = $(docdir)/$(subdir)
examples_DATA = $(DIST_SOURCES) $(EXTRA_DIST)

MOSTLYCLEANFILES = $(noinst_DATA)

# for silent automake rules
AM_V_JAVAC = $(am__v_JAVAC_$(V))
am__v_JAVAC_ = $(am__v_JAVAC_$(AM_DEFAULT_VERBOSITY))
am__v_JAVAC_0 = @echo "  JAVAC " $@;
