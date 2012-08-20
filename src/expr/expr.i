%{
#include "expr/expr.h"
%}

%rename(apply) CVC4::ExprHashFunction::operator()(CVC4::Expr) const;

%ignore CVC4::operator<<(std::ostream&, const Expr&);
%ignore CVC4::operator<<(std::ostream&, const TypeCheckingException&);

%ignore CVC4::expr::operator<<(std::ostream&, ExprSetDepth);
%ignore CVC4::expr::operator<<(std::ostream&, ExprPrintTypes);
%ignore CVC4::expr::operator<<(std::ostream&, ExprDag);
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

%template(getConstTypeConstant) CVC4::Expr::getConst<CVC4::TypeConstant>;
%template(getConstArrayStoreAll) CVC4::Expr::getConst<CVC4::ArrayStoreAll>;
%template(getConstBitVectorSize) CVC4::Expr::getConst<CVC4::BitVectorSize>;
%template(getConstAscriptionType) CVC4::Expr::getConst<CVC4::AscriptionType>;
%template(getConstBitVectorBitOf) CVC4::Expr::getConst<CVC4::BitVectorBitOf>;
%template(getConstSubrangeBounds) CVC4::Expr::getConst<CVC4::SubrangeBounds>;
%template(getConstBitVectorRepeat) CVC4::Expr::getConst<CVC4::BitVectorRepeat>;
%template(getConstBitVectorExtract) CVC4::Expr::getConst<CVC4::BitVectorExtract>;
%template(getConstBitVectorRotateLeft) CVC4::Expr::getConst<CVC4::BitVectorRotateLeft>;
%template(getConstBitVectorSignExtend) CVC4::Expr::getConst<CVC4::BitVectorSignExtend>;
%template(getConstBitVectorZeroExtend) CVC4::Expr::getConst<CVC4::BitVectorZeroExtend>;
%template(getConstBitVectorRotateRight) CVC4::Expr::getConst<CVC4::BitVectorRotateRight>;
%template(getConstUninterpretedConstant) CVC4::Expr::getConst<CVC4::UninterpretedConstant>;
%template(getConstKind) CVC4::Expr::getConst<CVC4::kind::Kind_t>;
%template(getConstDatatype) CVC4::Expr::getConst<CVC4::Datatype>;
%template(getConstRational) CVC4::Expr::getConst<CVC4::Rational>;
%template(getConstBitVector) CVC4::Expr::getConst<CVC4::BitVector>;
%template(getConstPredicate) CVC4::Expr::getConst<CVC4::Predicate>;
%template(getConstString) CVC4::Expr::getConst<std::string>;
%template(getConstBoolean) CVC4::Expr::getConst<bool>;

%include "expr/expr.h"
