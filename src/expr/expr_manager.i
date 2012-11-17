%{
#include "expr/expr_manager.h"
%}

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
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Rational>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Predicate>;
%template(mkConst) CVC4::ExprManager::mkConst<std::string>;
%template(mkConst) CVC4::ExprManager::mkConst<bool>;

%include "expr/expr_manager.h"
