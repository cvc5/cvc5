%{
#include "util/datatype.h"
%}

%rename(equals) CVC4::Datatype::operator==(const Datatype&) const;
%ignore CVC4::Datatype::operator!=(const Datatype&) const;

%rename(beginConst) CVC4::Datatype::begin() const;
%rename(endConst) CVC4::Datatype::end() const;

%rename(getConstructor) CVC4::Datatype::operator[](size_t) const;

%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype*) const;
%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype::Constructor&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype::Constructor*) const;

%ignore CVC4::operator<<(std::ostream&, const Datatype&);
%ignore CVC4::operator<<(std::ostream&, const Datatype::Constructor&);
%ignore CVC4::operator<<(std::ostream&, const Datatype::Constructor::Arg&);

%include "util/datatype.h"
