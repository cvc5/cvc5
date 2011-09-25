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
	-I@srcdir@/../../../include -I@srcdir@/../../.. -I@builddir@/../../.. -I@builddir@/cvc3
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

lib_LTLIBRARIES =
data_DATA =

if CVC4_LANGUAGE_BINDING_JAVA

lib_LTLIBRARIES += libcvc4bindings_java_compat.la
data_DATA += cvc4compat.jar
libcvc4bindings_java_compat_la_LDFLAGS = \
	-version-info $(LIBCVC4BINDINGS_VERSION)
libcvc4bindings_java_compat_la_LIBADD = \
	-L@builddir@/../compat -lcvc4compat

endif

# source files
# java files of the library wrapper
LIB_FILES = \
	JniUtils \
	Cvc3Exception TypecheckException SoundException EvalException \
	CLException ParserException SmtlibException DebugException \
	Embedded EmbeddedManager \
	InputLanguage QueryResult SatResult FormulaValue \
	Expr ExprMut ExprManager ExprManagerMut \
	Type TypeMut Op OpMut Rational RationalMut \
	Theorem TheoremMut Proof ProofMut Context ContextMut \
	Flag Flags FlagsMut \
	Statistics StatisticsMut ValidityChecker
# java files of the test program
TEST_FILES = Test
# java files of the stand alone program
PROG_FILES = TimeoutHandler Cvc3
# all java files, library and stand alone
JAVA_FILES = $(LIB_FILES) $(TEST_FILES) $(PROG_FILES)
# jni files of the library wrapper
JNI_FILES = \
	EmbeddedManager \
	Expr ExprMut ExprManager \
	Type TypeMut Op OpMut Rational RationalMut \
	Theorem TheoremMut Proof ProofMut Context ContextMut \
	Flag Flags FlagsMut \
	Statistics StatisticsMut ValidityChecker

# stub files
IMPL_FILES = $(addsuffix _impl.cpp,$(JNI_FILES))
# generated files
JNI_CPP_FILES = $(patsubst %,%.cpp,$(JNI_FILES))
# non-generated files
SRC_CPP_FILES = JniUtils.cpp 
# all cpp files (to compile)
CPP_FILES = $(SRC_CPP_FILES) $(JNI_CPP_FILES)

nodist_libcvc4bindings_java_compat_la_SOURCES = $(CPP_FILES)

HEADER_FILES = JniUtils.h
PYTHON_FILES = run_all.py run_tests.py create_impl.py
MANIFEST_FILES = Cvc3_manifest Test_manifest

# compile each cpp file
$(JNI_CPP_FILES): %.cpp: %_impl.cpp $(builddir)%.h JniUtils.h
	$(AM_V_GEN)$(PYTHON) ./create_impl.py \
		$(HEADER_PATH)/$(PACKAGE)/$*.h \
		$(SOURCE_PATH)/$(PACKAGE)/$*_impl.cpp \
		$(SOURCE_PATH)/$(PACKAGE)/$*.cpp

$(SRC_CPP_FILES:.cpp=.lo): %.lo: src/cvc3/%.cpp .headers
	$(AM_V_CXX)$(LTCXXCOMPILE) -c $(JAVA_INCLUDES) -I . -o $@ $<

$(LIB_FILES:%=classes/cvc3/%.class): .classes
.classes:
	$(AM_V_GEN)mkdir -p classes && $(JAVAC) -source 1.4 -sourcepath $(srcdir)/src -d classes $(LIB_FILES:%=$(srcdir)/src/cvc3/%.java)
	@touch .classes
.headers: $(LIB_FILES:%=cvc3/%.h)
	@touch .headers
$(LIB_FILES:%=cvc3/%.h): %.h: classes/%.class .cvc3dir
	$(AM_V_GEN)$(JAVAH) -jni -force -classpath classes -o $@ cvc3.$(@:cvc3/%.h=%)
.cvc3dir:
	@mkdir -p cvc3 && touch $@
cvc4compat.jar: $(LIB_FILES:%=classes/cvc3/%.class)
	$(AM_V_GEN)$(JAR) cf $@ -C classes .

clean-local:
	rm -fr classes cvc3
CLEANFILES = .cvc3dir .classes .headers cvc4compat.jar
