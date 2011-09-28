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
	-L@builddir@/../../../compat -lcvc4compat

endif

# source files
# java files of the library wrapper
LIB_FILES = \
	JniUtils \
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
JAVA_FILES = $(LIB_FILES) $(TEST_FILES) $(PROG_FILES)
# jni files of the library wrapper
JNI_FILES = \
	EmbeddedManager \
	Expr \
	ExprMut \
	ExprManager \
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

# stub files
IMPL_FILES = $(patsubst %,src/cvc3/%_impl.cpp,$(JNI_FILES))
# generated files
JNI_CPP_FILES = $(patsubst %,%.cpp,$(JNI_FILES))
# non-generated files
SRC_CPP_FILES = src/cvc3/JniUtils.cpp
# all cpp files (to compile)
CPP_FILES = $(SRC_CPP_FILES) $(JNI_CPP_FILES)

dist_libcvc4bindings_java_compat_la_SOURCES = $(SRC_CPP_FILES) $(IMPL_FILES)
nodist_libcvc4bindings_java_compat_la_SOURCES = $(JNI_CPP_FILES)
BUILT_SOURCES = $(JNI_CPP_FILES)

EXTRA_DIST =
	formula_value.h \
	create_impl.py \
	Cvc3_manifest \
	src/cvc3/JniUtils.java \
	src/cvc3/Cvc3Exception.java \
	src/cvc3/TypecheckException.java \
	src/cvc3/SoundException.java \
	src/cvc3/EvalException.java \
	src/cvc3/CLException.java \
	src/cvc3/ParserException.java \
	src/cvc3/SmtlibException.java \
	src/cvc3/DebugException.java \
	src/cvc3/Embedded.java \
	src/cvc3/EmbeddedManager.java \
	src/cvc3/InputLanguage.java \
	src/cvc3/QueryResult.java \
	src/cvc3/SatResult.java \
	src/cvc3/FormulaValue.java \
	src/cvc3/Expr.java \
	src/cvc3/ExprMut.java \
	src/cvc3/ExprManager.java \
	src/cvc3/ExprManagerMut.java \
	src/cvc3/Type.java \
	src/cvc3/TypeMut.java \
	src/cvc3/Op.java \
	src/cvc3/OpMut.java \
	src/cvc3/Rational.java \
	src/cvc3/RationalMut.java \
	src/cvc3/Theorem.java \
	src/cvc3/TheoremMut.java \
	src/cvc3/Proof.java \
	src/cvc3/ProofMut.java \
	src/cvc3/Context.java \
	src/cvc3/ContextMut.java \
	src/cvc3/Flag.java \
	src/cvc3/Flags.java \
	src/cvc3/FlagsMut.java \
	src/cvc3/Statistics.java \
	src/cvc3/StatisticsMut.java \
	src/cvc3/ValidityChecker.java

# compile each cpp file
$(JNI_CPP_FILES): %.cpp: src/cvc3/%_impl.cpp $(builddir)/cvc3/%.h include/cvc3/JniUtils.h
	$(AM_V_GEN)$(PYTHON) $(srcdir)/create_impl.py \
		cvc3/$*.h \
		$(srcdir)/src/cvc3/$*_impl.cpp \
		$*.cpp

JniUtils.lo: src/cvc3/JniUtils.cpp .headers
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
