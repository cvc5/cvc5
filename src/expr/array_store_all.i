%{
#include "expr/array_store_all.h"
%}

%rename(equals) CVC4::ArrayStoreAll::operator==(const ArrayStoreAll&) const;
%ignore CVC4::ArrayStoreAll::operator!=(const ArrayStoreAll&) const;
%rename(less) CVC4::ArrayStoreAll::operator<(const ArrayStoreAll&) const;
%rename(lessEqual) CVC4::ArrayStoreAll::operator<=(const ArrayStoreAll&) const;
%rename(greater) CVC4::ArrayStoreAll::operator>(const ArrayStoreAll&) const;
%rename(greaterEqual) CVC4::ArrayStoreAll::operator>=(const ArrayStoreAll&) const;

%rename(apply) CVC4::ArrayStoreAllHashFunction::operator()(const ArrayStoreAll&) const;

%ignore CVC4::operator<<(std::ostream&, const ArrayStoreAll&);

%include "expr/type.i"
%include "expr/array_store_all.h"
