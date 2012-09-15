%{
#include "util/datatype.h"
%}

%extend std::vector< CVC4::Datatype > {
  /* These member functions have slightly different signatures in
   * different swig language packages.  The underlying issue is that
   * DatatypeConstructor doesn't have a default constructor */
#ifdef SWIGOCAML
  %ignore vector(unsigned int size = 0);// ocaml
  %ignore set( int i, const CVC4::Datatype &x );// ocaml
  %ignore to_array();// ocaml
#endif /* SWIGOCAML */
  %ignore vector(size_type);// java/python/perl/others?
  %ignore resize(size_type);// java/python/perl/others?
  %ignore set(int i, const CVC4::Datatype& x);
  %ignore to_array();
};
%template(vectorDatatype) std::vector< CVC4::Datatype >;

%extend std::vector< CVC4::DatatypeConstructor > {
  /* These member functions have slightly different signatures in
   * different swig language packages.  The underlying issue is that
   * DatatypeConstructor doesn't have a default constructor */
#ifdef SWIGOCAML
  %ignore vector(unsigned int size = 0);// ocaml
  %ignore set( int i, const CVC4::DatatypeConstructor &x );// ocaml
  %ignore to_array();// ocaml
#endif /* SWIGOCAML */
  %ignore vector(size_type);// java/python/perl/others?
  %ignore resize(size_type);// java/python/perl/others?
  %ignore set(int i, const CVC4::Datatype::Constructor& x);
  %ignore to_array();
};
%template(vectorDatatypeConstructor) std::vector< CVC4::DatatypeConstructor >;

%rename(equals) CVC4::Datatype::operator==(const Datatype&) const;
%ignore CVC4::Datatype::operator!=(const Datatype&) const;

%rename(beginConst) CVC4::Datatype::begin() const;
%rename(endConst) CVC4::Datatype::end() const;

%rename(getConstructor) CVC4::Datatype::operator[](size_t) const;

%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype*) const;
%rename(apply) CVC4::DatatypeHashFunction::operator()(const DatatypeConstructor&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const DatatypeConstructor*) const;

%rename(beginConst) CVC4::DatatypeConstructor::begin() const;
%rename(endConst) CVC4::DatatypeConstructor::end() const;

%rename(getArg) CVC4::DatatypeConstructor::operator[](size_t) const;

%ignore CVC4::operator<<(std::ostream&, const Datatype&);
%ignore CVC4::operator<<(std::ostream&, const DatatypeConstructor&);
%ignore CVC4::operator<<(std::ostream&, const DatatypeConstructorArg&);

%feature("valuewrapper") CVC4::DatatypeUnresolvedType;
%feature("valuewrapper") CVC4::DatatypeConstructor;

%include "util/datatype.h"

