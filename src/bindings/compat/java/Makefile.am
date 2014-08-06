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
	-I@builddir@/../../.. -I@srcdir@/../../../include -I@srcdir@/../../.. \
	-I@builddir@/cvc3 -I@srcdir@/include/cvc3
AM_CXXFLAGS = -Wall -Wno-unused-variable

javadatadir = $(datadir)/java
javalibdir = $(libdir)/jni
javadata_DATA =
javalib_LTLIBRARIES=
BUILT_SOURCES =

if CVC4_LANGUAGE_BINDING_JAVA

javalib_LTLIBRARIES += libcvc4compatjni.la
javadata_DATA += CVC4compat.jar
libcvc4compatjni_la_LDFLAGS = \
	-module \
	-shrext $(CVC4_JAVA_MODULE_EXT) \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4compatjni_la_LIBADD = \
	@builddir@/../../../compat/libcvc4compat.la \
	@builddir@/../../../libcvc4.la
BUILT_SOURCES += $(JNI_CPP_FILES)

endif

# source files
# java files of the library wrapper
LIB_FILES = \
	Cvc3Exception \
	TypecheckException \
	SoundException \
	EvalException \
	CLException \
	ParserException \
	SmtlibException \
	DebugException \
	Embedded \
	EmbeddedManager \
	InputLanguage \
	QueryResult \
	SatResult \
	FormulaValue \
	Expr \
	ExprMut \
	ExprManager \
	ExprManagerMut \
	Type \
	TypeMut \
	Op \
	OpMut \
	Rational \
	RationalMut \
	Theorem \
	TheoremMut \
	Proof \
	ProofMut \
	Context \
	ContextMut \
	Flag \
	Flags \
	FlagsMut \
	Statistics \
	StatisticsMut \
	ValidityChecker

# java files of the test program
TEST_FILES = Test
# java files of the stand alone program
PROG_FILES = TimeoutHandler Cvc3
# all java files, library and stand alone
JAVA_FILES = JniUtils $(LIB_FILES) $(TEST_FILES) $(PROG_FILES)
# generated files
JNI_CPP_FILES = \
	EmbeddedManager.cpp \
	Expr.cpp \
	ExprMut.cpp \
	ExprManager.cpp \
	ValidityChecker.cpp
#	Type.cpp \
#	TypeMut.cpp \
#	Op.cpp \
#	OpMut.cpp \
#	Rational.cpp \
#	RationalMut.cpp \
#	Theorem.cpp \
#	TheoremMut.cpp \
#	Proof.cpp \
#	ProofMut.cpp \
#	Context.cpp \
#	ContextMut.cpp \
#	Flag.cpp \
#	Flags.cpp \
#	FlagsMut.cpp \
#	Statistics.cpp \
#	StatisticsMut.cpp \
# non-generated files
SRC_CPP_FILES = src/cvc3/JniUtils.cpp
# all cpp files (to compile)
CPP_FILES = $(SRC_CPP_FILES) $(JNI_CPP_FILES)

dist_libcvc4compatjni_la_SOURCES = $(SRC_CPP_FILES) include/cvc3/JniUtils.h
nodist_libcvc4compatjni_la_SOURCES = $(JNI_CPP_FILES)

EXTRA_DIST = \
	formula_value.h \
	create_impl.py \
	Cvc3_manifest \
	$(JNI_CPP_FILES:%.cpp=src/cvc3/%_impl.cpp) \
	$(JAVA_FILES:%=src/cvc3/%.java)

# compile each cpp file
$(JNI_CPP_FILES): %.cpp: src/cvc3/%_impl.cpp $(builddir)/cvc3/%.h include/cvc3/JniUtils.h
	$(AM_V_GEN)$(PYTHON) $(srcdir)/create_impl.py \
		cvc3/$*.h \
		$(srcdir)/src/cvc3/$*_impl.cpp \
		$*.cpp

JniUtils.lo: src/cvc3/JniUtils.cpp .headers
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_INCLUDES) $(JAVA_CPPFLAGS) -I . -o $@ $<
%.lo: %.cpp .headers
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_INCLUDES) $(JAVA_CPPFLAGS) -I . -o $@ $<

$(LIB_FILES:%=classes/cvc3/%.class) classes/cvc3/JniUtils.class: .classes
.classes:
	$(AM_V_GEN)mkdir -p classes && $(JAVAC) -source 1.4 -target 1.4 -sourcepath $(srcdir)/src -d classes $(LIB_FILES:%=$(srcdir)/src/cvc3/%.java)
	@touch .classes
.headers: $(LIB_FILES:%=cvc3/%.h)
	@touch .headers
$(LIB_FILES:%=cvc3/%.h): %.h: classes/%.class .cvc3dir
	$(AM_V_GEN)$(JAVAH) -jni -force -classpath classes -o $@ cvc3.$(@:cvc3/%.h=%)
.cvc3dir:
	@mkdir -p cvc3 && touch $@
CVC4compat.jar: $(LIB_FILES:%=classes/cvc3/%.class) classes/cvc3/JniUtils.class
	$(AM_V_GEN)$(JAR) cf $@ -C classes .

clean-local:
	rm -fr classes cvc3
MOSTLYCLEANFILES = .cvc3dir .classes .headers CVC4compat.jar $(JNI_CPP_FILES)
