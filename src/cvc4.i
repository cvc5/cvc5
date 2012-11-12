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
  template <class K, class V, class H> class hash_map {};
}

%{
// Perl's headers define "seed" to Perl_seed, which breaks
// gmpxx.h; undo the damage for our CVC4 module.
#ifdef SWIGPERL
#  undef seed
#endif /* SWIGPERL */

// OCaml's headers define "invalid_argument" and "flush" to
// caml_invalid_argument and caml_flush, which breaks C++
// standard headers; undo this damage
//
// Unfortunately, this code isn't inserted early enough.  swig puts
// an include <stdexcept> very early, which breaks linking due to a
// nonexistent std::caml_invalid_argument symbol.. ridiculous!
//
#ifdef SWIGOCAML
#  if defined(flush) || defined(invalid_argument)
#    error "flush" or "invalid_argument" (or both) is defined by the ocaml headers.  You must #undef it above before inclusion of <stdexcept>.
#  endif /* flush */
#  undef flush
#  undef invalid_argument
#endif /* SWIGOCAML */

namespace CVC4 {}
using namespace CVC4;

#include <iostream>
#include <vector>
#include <set>
#include <string>
#include <ext/hash_map>
#include <typeinfo>
#include <cassert>

#include "util/sexpr.h"
#include "util/exception.h"
#include "expr/type.h"
#include "expr/expr.h"
#include "util/datatype.h"
#include "expr/command.h"
%}

%template(vectorCommandPtr) std::vector< CVC4::Command* >;
%template(vectorType) std::vector< CVC4::Type >;
%template(vectorExpr) std::vector< CVC4::Expr >;
%template(vectorDatatypeType) std::vector< CVC4::DatatypeType >;
%template(vectorSExpr) std::vector< CVC4::SExpr >;
%template(vectorString) std::vector< std::string >;
%template(setType) std::set< CVC4::Type >;
%template(hashmapExpr) std::hash_map< CVC4::Expr, CVC4::Expr, CVC4::ExprHashFunction >;

// This is unfortunate, but seems to be necessary; if we leave NULL
// defined, swig will expand it to "(void*) 0", and some of swig's
// helper functions won't compile properly.
#undef NULL

#ifdef SWIGJAVA

%exception {
  try {
    $action
  } catch(CVC4::Exception& e) {
    std::stringstream ss;
    ss << e.what() << ": " << e.getMessage();
    std::string explanation = ss.str();
    SWIG_JavaThrowException(jenv, SWIG_JavaRuntimeException, explanation.c_str());
  }
}

// Create a mapping from C++ Exceptions to Java Exceptions.
// This is in a couple of throws typemaps, simply because it's sensitive to SWIG's concept of which namespace we're in.
%typemap(throws) Exception %{
  jclass clazz = jenv->FindClass("edu/nyu/acsys/CVC4/$1_type");
  assert(clazz != NULL && jenv->ExceptionOccurred() == NULL);
  jmethodID method = jenv->GetMethodID(clazz, "<init>", "(JZ)V");
  assert(method != NULL && jenv->ExceptionOccurred() == NULL);
  jthrowable t = static_cast<jthrowable>(jenv->NewObject(clazz, method, reinterpret_cast<long>(new $1_type($1)), true));
  assert(t != NULL && jenv->ExceptionOccurred() == NULL);
  int status = jenv->Throw(t);
  assert(status == 0);
%}
%typemap(throws) CVC4::Exception %{
  std::string name = "edu/nyu/acsys/$1_type";
  for(size_t i = name.find("::"); i != std::string::npos; i = name.find("::")) {
    name.replace(i, 2, "/");
  }
  jclass clazz = jenv->FindClass(name.c_str());
  assert(clazz != NULL && jenv->ExceptionOccurred() == NULL);
  jmethodID method = jenv->GetMethodID(clazz, "<init>", "(JZ)V");
  assert(method != NULL && jenv->ExceptionOccurred() == NULL);
  jthrowable t = static_cast<jthrowable>(jenv->NewObject(clazz, method, reinterpret_cast<long>(new $1_type($1)), true));
  assert(t != NULL && jenv->ExceptionOccurred() == NULL);
  int status = jenv->Throw(t);
  assert(status == 0);
%}

%typemap(throws) ModalException = Exception;
%typemap(throws) LogicException = Exception;
%typemap(throws) OptionException = Exception;
%typemap(throws) IllegalArgumentException = Exception;
%typemap(throws) AssertionException = Exception;

%typemap(throws) CVC4::TypeCheckingException = CVC4::Exception;
%typemap(throws) CVC4::ScopeException = CVC4::Exception;
%typemap(throws) CVC4::IllegalArgumentException = CVC4::Exception;
%typemap(throws) CVC4::AssertionException = CVC4::Exception;
%typemap(throws) CVC4::parser::InputStreamException = CVC4::Exception;
%typemap(throws) CVC4::parser::ParserException = CVC4::Exception;

// Generate an error if the mapping from C++ CVC4 Exception to Java CVC4 Exception doesn't exist above
%typemap(throws) SWIGTYPE, SWIGTYPE &, SWIGTYPE *, SWIGTYPE [], SWIGTYPE [ANY] %{
#error "exception $1_type doesn't map to Java correctly---please edit src/cvc4.i and add it"
%}

%include "java/typemaps.i" // primitive pointers and references
%include "java/std_string.i" // map std::string to java.lang.String
%include "java/arrays_java.i" // C arrays to Java arrays
%include "java/various.i" // map char** to java.lang.String[]

#endif /* SWIGJAVA */

%include "util/integer.i"
%include "util/rational.i"
%include "util/statistics.i"
%include "util/exception.i"
%include "util/language.i"
%include "options/options.i"
%include "util/cardinality.i"
%include "util/bool.i"
%include "util/sexpr.i"
%include "util/output.i"
%include "util/result.i"
%include "util/configuration.i"
%include "util/bitvector.i"
%include "util/subrange_bound.i"
%include "util/array.i"
%include "util/array_store_all.i"
%include "util/hash.i"

%include "expr/type.i"
%include "util/ascription_type.i"
%include "util/datatype.i"

%include "expr/kind.i"
%include "expr/expr.i"
%include "expr/command.i"
%include "expr/symbol_table.i"
%include "expr/expr_manager.i"
%include "expr/expr_stream.i"

%include "smt/smt_engine.i"
%include "smt/modal_exception.i"
%include "smt/logic_exception.i"

%include "options/options.i"
%include "options/option_exception.i"

%include "parser/cvc4parser.i"
