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

%include "expr/expr_manager.h"

%template(mkConst) CVC4::ExprManager::mkConst< CVC4::Integer >;
%template(mkConst) CVC4::ExprManager::mkConst< CVC4::Rational >;

%include "expr/expr_manager.h"
