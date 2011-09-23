%{
#include "util/datatype.h"
namespace CVC4 {
//typedef CVC4::Datatype::Constructor DatatypeConstructor;
}
%}

namespace CVC4 {
%rename(DatatypeConstructor) CVC4::Datatype::Constructor;
//%rename(DatatypeConstructor) CVC4::Constructor;
}

%extend std::vector< CVC4::Datatype > {
  %ignore vector(size_type);
};
%template(vectorDatatype) std::vector< CVC4::Datatype >;

%extend std::vector< CVC4::Datatype::Constructor > {
  %ignore vector(size_type);
};
%template(vectorDatatypeConstructor) std::vector< CVC4::Datatype::Constructor >;

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
