%{
#include "expr/type.h"
%}

%rename(apply) CVC4::TypeHashFunction::operator()(const CVC4::Type&) const;

%ignore CVC4::operator<<(std::ostream&, const Type&);

%rename(assign) CVC4::Type::operator=(const Type&);
%rename(equals) CVC4::Type::operator==(const Type&) const;
%ignore CVC4::Type::operator!=(const Type&) const;
%rename(less) CVC4::Type::operator<(const Type&) const;
%rename(lessEqual) CVC4::Type::operator<=(const Type&) const;
%rename(greater) CVC4::Type::operator>(const Type&) const;
%rename(greaterEqual) CVC4::Type::operator>=(const Type&) const;

namespace CVC4 {
  namespace expr {
    %ignore exportTypeInternal;
  }/* CVC4::expr namespace */
}/* CVC4 namespace */

%include "expr/type.h"
