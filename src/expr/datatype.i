%{
#include "expr/datatype.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

#endif /* SWIGJAVA */
%}

%extend std::vector< CVC4::Datatype > {
  /* These member functions have slightly different signatures in
   * different swig language packages.  The underlying issue is that
   * DatatypeConstructor doesn't have a default constructor */
#if defined(SWIGOCAML) || defined(SWIGPERL) || defined(SWIGTCL)
  %ignore vector(unsigned int size = 0);
  %ignore set( int i, const CVC4::Datatype &x );
  %ignore to_array();
#endif /* SWIGOCAML || SWIGPERL || SWIGTCL */
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
#if defined(SWIGOCAML) || defined(SWIGPERL) || defined(SWIGTCL)
  %ignore vector(unsigned int size = 0);
  %ignore set( int i, const CVC4::DatatypeConstructor &x );
  %ignore to_array();
#endif /* SWIGOCAML || SWIGPERL || SWIGTCL */
  %ignore vector(size_type);// java/python/perl/others?
  %ignore resize(size_type);// java/python/perl/others?
  %ignore set(int i, const CVC4::Datatype::Constructor& x);
  %ignore to_array();
};
//%template(vectorDatatypeConstructor) std::vector< CVC4::DatatypeConstructor >;

%rename(equals) CVC4::Datatype::operator==(const Datatype&) const;
%ignore CVC4::Datatype::operator!=(const Datatype&) const;

%ignore CVC4::Datatype::begin();
%ignore CVC4::Datatype::end();
%ignore CVC4::Datatype::begin() const;
%ignore CVC4::Datatype::end() const;

%rename(get) CVC4::Datatype::operator[](size_t) const;
%rename(get) CVC4::Datatype::operator[](std::string) const;

%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype*) const;
%rename(apply) CVC4::DatatypeHashFunction::operator()(const DatatypeConstructor&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const DatatypeConstructor*) const;

%ignore CVC4::DatatypeConstructor::begin();
%ignore CVC4::DatatypeConstructor::end();
%ignore CVC4::DatatypeConstructor::begin() const;
%ignore CVC4::DatatypeConstructor::end() const;

%rename(get) CVC4::DatatypeConstructor::operator[](size_t) const;
%rename(get) CVC4::DatatypeConstructor::operator[](std::string) const;

%ignore CVC4::operator<<(std::ostream&, const Datatype&);
%ignore CVC4::operator<<(std::ostream&, const DatatypeConstructor&);
%ignore CVC4::operator<<(std::ostream&, const DatatypeConstructorArg&);

%ignore CVC4::DatatypeConstructorIterator;
%ignore CVC4::DatatypeConstructorArgIterator;

%feature("valuewrapper") CVC4::DatatypeUnresolvedType;
%feature("valuewrapper") CVC4::DatatypeConstructor;


%rename(equals) CVC4::DatatypeIndexConstant::operator==(const DatatypeIndexConstant&) const;
%ignore CVC4::DatatypeIndexConstant::operator!=(const DatatypeIndexConstant&) const;

%rename(less) CVC4::DatatypeIndexConstant::operator<(const DatatypeIndexConstant&) const;
%rename(lessEqual) CVC4::DatatypeIndexConstant::operator<=(const DatatypeIndexConstant&) const;
%rename(greater) CVC4::DatatypeIndexConstant::operator>(const DatatypeIndexConstant&) const;
%rename(greaterEqual) CVC4::DatatypeIndexConstant::operator>=(const DatatypeIndexConstant&) const;

%rename(apply) CVC4::DatatypeIndexConstantFunction::operator()(const DatatypeIndexConstant&) const;

%ignore CVC4::operator<<(std::ostream& out, const DatatypeIndexConstant& es);


#ifdef SWIGJAVA

// Instead of Datatype::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%extend CVC4::Datatype {
  CVC4::JavaIteratorAdapter<CVC4::Datatype> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::Datatype>(*$self);
  }

  std::string toString() const {
    std::stringstream ss;
    ss << *$self;
    return ss.str();
  }
}
%extend CVC4::DatatypeConstructor {
  CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor>(*$self);
  }

  std::string toString() const {
    std::stringstream ss;
    ss << *$self;
    return ss.str();
  }
}
%extend CVC4::DatatypeConstructorArg {
  std::string toString() const {
    std::stringstream ss;
    ss << *$self;
    return ss.str();
  }
}

// Datatype is "iterable" on the Java side
%typemap(javainterfaces) CVC4::Datatype "java.lang.Iterable<DatatypeConstructor>";
%typemap(javainterfaces) CVC4::DatatypeConstructor "java.lang.Iterable<DatatypeConstructorArg>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::Datatype> "class";
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::Datatype> "java.util.Iterator<DatatypeConstructor>";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor> "java.util.Iterator<DatatypeConstructorArg>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::Datatype> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public DatatypeConstructor next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public DatatypeConstructorArg next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"
// getNext() just allows C++ iterator access from Java-side next(), make it private
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::Datatype>::getNext() "private";
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor>::getNext() "private";

// map the types appropriately.
%typemap(jni) CVC4::Datatype::iterator::value_type "jobject";
%typemap(jtype) CVC4::Datatype::iterator::value_type "edu.nyu.acsys.CVC4.DatatypeConstructor";
%typemap(jstype) CVC4::Datatype::iterator::value_type "edu.nyu.acsys.CVC4.DatatypeConstructor";
%typemap(javaout) CVC4::Datatype::iterator::value_type { return $jnicall; }
%typemap(jni) CVC4::DatatypeConstructor::iterator::value_type "jobject";
%typemap(jtype) CVC4::DatatypeConstructor::iterator::value_type "edu.nyu.acsys.CVC4.DatatypeConstructorArg";
%typemap(jstype) CVC4::DatatypeConstructor::iterator::value_type "edu.nyu.acsys.CVC4.DatatypeConstructorArg";
%typemap(javaout) CVC4::DatatypeConstructor::iterator::value_type { return $jnicall; }

#endif /* SWIGJAVA */

%include "expr/datatype.h"

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"

%template(JavaIteratorAdapter_Datatype) CVC4::JavaIteratorAdapter<CVC4::Datatype>;
%template(JavaIteratorAdapter_DatatypeConstructor) CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor>;

#endif /* SWIGJAVA */
