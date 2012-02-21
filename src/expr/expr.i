%{
#include "expr/expr.h"
%}

%rename(apply) CVC4::ExprHashFunction::operator()(CVC4::Expr) const;

%ignore CVC4::operator<<(std::ostream&, const Expr&);
%ignore CVC4::operator<<(std::ostream&, const TypeCheckingException&);

%ignore CVC4::expr::operator<<(std::ostream&, ExprSetDepth);
%ignore CVC4::expr::operator<<(std::ostream&, ExprPrintTypes);
%ignore CVC4::expr::operator<<(std::ostream&, ExprSetLanguage);

%rename(assign) CVC4::Expr::operator=(const Expr&);
%rename(equals) CVC4::Expr::operator==(const Expr&) const;
%ignore CVC4::Expr::operator!=(const Expr&) const;
%rename(less) CVC4::Expr::operator<(const Expr&) const;
%rename(lessEqual) CVC4::Expr::operator<=(const Expr&) const;
%rename(greater) CVC4::Expr::operator>(const Expr&) const;
%rename(greaterEqual) CVC4::Expr::operator>=(const Expr&) const;

%rename(getChild) CVC4::Expr::operator[](unsigned i) const;
%ignore CVC4::Expr::operator bool() const;// can just use isNull()

namespace CVC4 {
  namespace expr {
    %ignore exportInternal;
  }/* CVC4::expr namespace */
}/* CVC4 namespace */

%include "expr/expr.h"
