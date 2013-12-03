%{
#include "expr/expr_manager.h"
%}

%typemap(javacode) CVC4::ExprManager %{
  // a ref is kept here to keep Java GC from collecting the Options
  // before the ExprManager
  private Object options;
%}
%typemap(javaconstruct) CVC4::ExprManager {
    this($imcall, true);
    this.options = SmtEngine.mkRef(options); // keep ref to options in SWIG proxy class
  }
%typemap(javadestruct, methodname="delete", methodmodifiers="public synchronized") CVC4::ExprManager {
    SmtEngine.dlRef(options);
    options = null;
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        CVC4JNI.delete_SmtEngine(swigCPtr);
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

%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TypeConstant>;
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
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::UninterpretedConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::kind::Kind_t>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Datatype>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TupleSelect>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TupleUpdate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Record>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RecordSelect>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RecordUpdate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Rational>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Predicate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::String>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RegExp>;
%template(mkConst) CVC4::ExprManager::mkConst<bool>;

%include "expr/expr_manager.h"
