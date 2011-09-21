%import "bindings/swig.h"

%module CVC4
// nspace completely broken with Java packaging
//%nspace;

%{
namespace CVC4 { class Exception; }
using namespace CVC4;
%}

%exception {
  try {
    $action
  } catch(CVC4::Exception& e) {
    ::std::cerr << e << ::std::endl;
    jclass clazz = jenv->FindClass("java/lang/RuntimeException");
    jenv->ThrowNew(clazz, e.toString().c_str());
  }
}

%include "std_string.i" // map std::string to java.lang.String

%include "util/integer.i"
%include "util/rational.i"
%include "util/stats.i"
%include "util/exception.i"
%include "util/language.i"
%include "util/options.i"
%include "util/cardinality.i"
%include "util/bool.i"
%include "util/sexpr.i"
%include "util/datatype.i"
%include "util/output.i"
%include "util/result.i"
%include "util/configuration.i"
%include "util/Assert.i"
%include "util/bitvector.i"
%include "util/subrange_bound.i"
%include "util/array.i"
%include "util/ascription_type.i"
%include "util/pseudoboolean.i"
%include "util/hash.i"

%include "expr/command.i"
%include "expr/declaration_scope.i"
%include "expr/kind.i"
%include "expr/type.i"
%include "expr/expr.i"
%include "expr/expr_manager.i"

%include "smt/smt_engine.i"
%include "smt/bad_option_exception.i"
%include "smt/no_such_function_exception.i"
%include "smt/modal_exception.i"

%include "parser/cvc4parser.i"
