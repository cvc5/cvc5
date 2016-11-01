%{
#include "expr/expr_manager.h"
%}

%typemap(javacode) CVC4::ExprManager %{
  // a ref is kept here to keep Java GC from collecting the Options
  // before the ExprManager
  private Object options;
%}
%typemap(javaconstruct) ExprManager {
    this($imcall, true);
    this.options = SmtEngine.mkRef(options); // keep ref to options in SWIG proxy class
  }
%typemap(javadestruct, methodname="delete", methodmodifiers="public synchronized") CVC4::ExprManager {
    SmtEngine.dlRef(options);
    options = null;
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        CVC4JNI.delete_ExprManager(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

#ifdef SWIGOCAML
  /* OCaml bindings cannot deal with this degree of overloading */
  %ignore CVC4::ExprManager::mkExpr(Kind, const std::vector<Expr>&);
  %ignore CVC4::ExprManager::mkExpr(Kind, Expr, const std::vector<Expr>&);
  %ignore CVC4::ExprManager::mkExpr(Expr);
  %ignore CVC4::ExprManager::mkExpr(Expr, Expr);
  %ignore CVC4::ExprManager::mkExpr(Expr, Expr, Expr);
  %ignore CVC4::ExprManager::mkExpr(Expr, Expr, Expr, Expr);
  %ignore CVC4::ExprManager::mkExpr(Expr, Expr, Expr, Expr, Expr);
  %ignore CVC4::ExprManager::mkExpr(Expr, Expr, Expr, Expr, Expr, Expr);
  %ignore CVC4::ExprManager::mkExpr(Expr, const std::vector<Expr>&);
#endif /* SWIGOCAML */

%ignore CVC4::stats::getStatisticsRegistry(ExprManager*);

%include "expr/expr_manager.h"

%template(mkConst) CVC4::ExprManager::mkConst<CVC4::ArrayStoreAll>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorSize>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::AscriptionType>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorBitOf>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::SubrangeBounds>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorRepeat>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorExtract>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorRotateLeft>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorSignExtend>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorZeroExtend>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorRotateRight>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::IntToBitVector>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPoint>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RoundingMode>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointSize>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPIEEEBitVector>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPFloatingPoint>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPReal>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPSignedBitVector>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPUnsignedBitVector>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPGeneric>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToUBV>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToSBV>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::UninterpretedConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::kind::Kind_t>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::DatatypeIndexConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TupleUpdate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RecordUpdate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Rational>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Predicate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::EmptySet>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::String>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RegExp>;
#ifdef SWIGPYTHON
/* The python bindings cannot differentiate between bool and other basic
 * types like enum and int. Therefore, we rename mkConst for the bool
 * case into mkBoolConst.
*/
%template(mkBoolConst) CVC4::ExprManager::mkConst<bool>;

// These cases have trouble too.  Remove them for now.
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TypeConstant>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TupleSelect>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Record>;
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RecordSelect>;

#else
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TypeConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TupleSelect>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Record>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RecordSelect>;
%template(mkConst) CVC4::ExprManager::mkConst<bool>;
#endif

%include "expr/expr_manager.h"
