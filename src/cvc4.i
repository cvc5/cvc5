// Declare that all functions in the interface can throw exceptions of type
// CVC4::Exception and exceptions in general. SWIG catches those exceptions and
// turns them into target language exceptions via "throws" typemaps.
%catches(CVC4::Exception,...);

%import "bindings/swig.h"

%include "stdint.i"
%include "stl.i"

%module CVC4
// nspace completely broken with Java packaging
//%nspace;

namespace std {
  class istream;
  class ostream;
  template <class T> class set {};
  template <class K, class V, class H> class unordered_map {};
}

%{
namespace CVC4 {}
using namespace CVC4;

#include <cassert>
#include <unordered_map>
#include <iosfwd>
#include <set>
#include <string>
#include <typeinfo>
#include <vector>

#include "base/exception.h"
#include "base/modal_exception.h"
#include "expr/datatype.h"
#include "expr/expr.h"
#include "expr/type.h"
#include "options/option_exception.h"
#include "smt/command.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/integer.h"
#include "util/sexpr.h"
#include "util/unsafe_interrupt_exception.h"

#ifdef SWIGJAVA
#include "bindings/java_stream_adapters.h"
std::set<JavaInputStreamAdapter*> CVC4::JavaInputStreamAdapter::s_adapters;
#endif
%}

#ifdef SWIGPYTHON
%pythonappend CVC4::SmtEngine::SmtEngine %{
  # Hold a reference to the ExprManager to make sure that Python keeps the
  # ExprManager alive as long as the SmtEngine exists
  self.em = em
%}
#endif /* SWIGPYTHON */

%template(vectorType) std::vector< CVC4::Type >;
%template(vectorExpr) std::vector< CVC4::Expr >;
%template(vectorUnsignedInt) std::vector< unsigned int >;
%template(vectorVectorExpr) std::vector< std::vector< CVC4::Expr > >;
%template(vectorDatatypeType) std::vector< CVC4::DatatypeType >;
%template(vectorSExpr) std::vector< CVC4::SExpr >;
%template(vectorString) std::vector< std::string >;
%template(vectorPairStringType) std::vector< std::pair< std::string, CVC4::Type > >;
%template(pairStringType) std::pair< std::string, CVC4::Type >;
%template(setOfType) std::set< CVC4::Type >;
%template(hashmapExpr) std::unordered_map< CVC4::Expr, CVC4::Expr, CVC4::ExprHashFunction >;

// This is unfortunate, but seems to be necessary; if we leave NULL
// defined, swig will expand it to "(void*) 0", and some of swig's
// helper functions won't compile properly.
#undef NULL

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

// Map C++ exceptions of type CVC4::Exception to Java exceptions of type
// edu.stanford.CVC4.Exception
// 
// As suggested in:
// http://www.swig.org/Doc3.0/SWIGDocumentation.html#Java_exception_typemap
%typemap(throws, throws="edu.stanford.CVC4.Exception") CVC4::Exception {
  jclass excep = jenv->FindClass("edu/stanford/CVC4/Exception");
  if (excep)
    jenv->ThrowNew(excep, $1.what());
  return $null;
}

%include "java/typemaps.i" // primitive pointers and references
%include "java/std_string.i" // map std::string to java.lang.String
%include "java/arrays_java.i" // C arrays to Java arrays
%include "java/various.i" // map char** to java.lang.String[]

// Functions on the C++ side taking std::ostream& should on the Java side
// take a java.io.OutputStream.  A JavaOutputStreamAdapter is created in
// the wrapper which creates and passes on a std::stringstream to the C++
// function.  Then on exit, the string from the stringstream is dumped to
// the Java-side OutputStream.
%typemap(jni) std::ostream& "jlong"
%typemap(jtype) std::ostream& "long"
%typemap(jstype) std::ostream& "java.io.OutputStream"
%typemap(javain,
         pre="    edu.stanford.CVC4.JavaOutputStreamAdapter temp$javainput = new edu.stanford.CVC4.JavaOutputStreamAdapter();", pgcppname="temp$javainput",
         post="    new java.io.PrintStream($javainput).print(temp$javainput.toString());")
         std::ostream& "edu.stanford.CVC4.JavaOutputStreamAdapter.getCPtr(temp$javainput)"

%typemap(jni) std::istream& "jlong"
%typemap(jtype) std::istream& "long"
%typemap(jstype) std::istream& "java.io.InputStream"
%typemap(javain,
         pre="    edu.stanford.CVC4.JavaInputStreamAdapter temp$javainput = edu.stanford.CVC4.JavaInputStreamAdapter.get($javainput);", pgcppname="temp$javainput",
         post="")
         std::istream& "edu.stanford.CVC4.JavaInputStreamAdapter.getCPtr(temp$javainput)"
%typemap(in) jobject inputStream %{
  $1 = jenv->NewGlobalRef($input);
%}
%typemap(out) CVC4::JavaInputStreamAdapter* %{
  $1->pull(jenv);
  *(CVC4::JavaInputStreamAdapter **)&$result = $1;
%}
%typemap(javacode) CVC4::JavaInputStreamAdapter %{
  private static java.util.HashMap<java.io.InputStream, JavaInputStreamAdapter> streams =
    new java.util.HashMap<java.io.InputStream, JavaInputStreamAdapter>();
  public static JavaInputStreamAdapter get(java.io.InputStream is) {
    if(streams.containsKey(is)) {
      return (JavaInputStreamAdapter) streams.get(is);
    }
    JavaInputStreamAdapter adapter = new JavaInputStreamAdapter(is);
    streams.put(is, adapter);
    return adapter;
  }
%}
%typemap(javafinalize) CVC4::JavaInputStreamAdapter %{
  protected void finalize() {
    streams.remove(getInputStream());
    delete();
  }
%}
%ignore CVC4::JavaInputStreamAdapter::init(JNIEnv*);
%ignore CVC4::JavaInputStreamAdapter::pullAdapters(JNIEnv*);
%ignore CVC4::JavaInputStreamAdapter::pull(JNIEnv*);
%javamethodmodifiers CVC4::JavaInputStreamAdapter::getInputStream() const "private";
%javamethodmodifiers CVC4::JavaInputStreamAdapter::JavaInputStreamAdapter(jobject) "private";

%exception CVC4::JavaInputStreamAdapter::~JavaInputStreamAdapter() %{
  try {
    jenv->DeleteGlobalRef(arg1->getInputStream());
    $action
  } catch(CVC4::Exception& e) {
    std::stringstream ss;
    ss << e.what() << ": " << e.getMessage();
    std::string explanation = ss.str();
    SWIG_JavaThrowException(jenv, SWIG_JavaRuntimeException, explanation.c_str());
  }
%}

/* Copied (and modified) from java.swg; the standard swig version causes
 * negative BigInteger to be interpreted unsigned.  Here we throw an
 * exception. */
%typemap(in) unsigned long long {
  jclass clazz;
  jmethodID mid;
  jbyteArray ba;
  jbyte* bae;
  jsize sz;
  int i;

  if (!$input) {
    SWIG_JavaThrowException(jenv, SWIG_JavaNullPointerException, "BigInteger null");
    return $null;
  }
  clazz = JCALL1(GetObjectClass, jenv, $input);
  mid = JCALL3(GetMethodID, jenv, clazz, "toByteArray", "()[B");
  ba = (jbyteArray)JCALL2(CallObjectMethod, jenv, $input, mid);
  bae = JCALL2(GetByteArrayElements, jenv, ba, 0);
  sz = JCALL1(GetArrayLength, jenv, ba);
  if((bae[0] & 0x80) != 0) {
    SWIG_JavaThrowException(jenv, SWIG_JavaRuntimeException, "BigInteger argument must be nonnegative.");
  }
  jsize test_sz = sz;
  if(sz > 1 && bae[0] == 0) {
    --test_sz;
  }
  if(test_sz > sizeof(unsigned long long)) {
    SWIG_JavaThrowException(jenv, SWIG_JavaRuntimeException, "BigInteger argument out of bounds.");
  }
  $1 = 0;
  for(i=0; i<sz; i++) {
    $1 = ($1 << 8) | ($1_type)(unsigned char)bae[i];
  }
  JCALL3(ReleaseByteArrayElements, jenv, ba, bae, 0);
}

#endif /* SWIGJAVA */

// TIM:
// At the moment, the header includes seem to need to follow a special order.
// I don't know why. I am following the build order 
%include "base/configuration.i"
%include "base/exception.i"
%include "base/modal_exception.i"

%include "options/language.i"

// Tim: "util/integer.i" must come before util/{rational.i,bitvector.i}.
%include "util/integer.i"
%include "util/rational.i"
%include "util/bitvector.i"
%include "util/floatingpoint.i"

// Tim: The remainder of util/.
%include "util/bool.i"
%include "util/cardinality.i"
%include "util/hash.i"
%include "util/proof.i"
%include "util/regexp.i"
%include "util/result.i"
%include "util/sexpr.i"
%include "util/statistics.i"
%include "util/string.i"
%include "util/tuple.i"
%include "util/unsafe_interrupt_exception.i"

%include "expr/uninterpreted_constant.i"
%include "expr/array_store_all.i"
%include "expr/ascription_type.i"
%include "expr/emptyset.i"
%include "expr/expr_sequence.i"
%include "expr/datatype.i"
%include "expr/record.i"
%include "proof/unsat_core.i"

// TIM:
// Have these before the rest of expr/.
// Again, no clue why.
%include "expr/array.i"
%include "expr/kind.i"
%include "expr/type.i"

// TIM:
// The remainder of the includes:
%include "expr/expr.i"
%include "expr/expr_manager.i"
%include "expr/variable_type_map.i"
%include "options/option_exception.i"
%include "options/options.i"
%include "smt/logic_exception.i"
%include "theory/logic_info.i"
%include "theory/theory_id.i"

// Tim: This should come after "theory/logic_info.i".
%include "smt/smt_engine.i"
