%{
#include "expr/expr.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

#endif /* SWIGJAVA */
%}

#ifdef SWIGPYTHON
%rename(doApply) CVC4::ExprHashFunction::operator()(CVC4::Expr) const;
#else /* SWIGPYTHON */
%rename(apply) CVC4::ExprHashFunction::operator()(CVC4::Expr) const;
#endif /* SWIGPYTHON */

#ifdef SWIGJAVA
%typemap(javabody) CVC4::Expr %{
  private long swigCPtr;
  protected boolean swigCMemOwn;

  protected $javaclassname(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = SmtEngine.mkRef(getExprManager()); // keep ref to em in SWIG proxy class
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}
%javamethodmodifiers CVC4::Expr::operator=(const Expr&) "protected";
%typemap(javacode) CVC4::Expr %{
  // a ref is kept here to keep Java GC from collecting the ExprManager
  // before the Expr
  private Object em;

  public Expr assign(Expr e) {
    Expr r = assignInternal(e);
    this.em = SmtEngine.mkRef(getExprManager()); // keep ref to em in SWIG proxy class
    return r;
  }
%}
%typemap(javaconstruct) Expr {
    this($imcall, true);
    this.em = SmtEngine.mkRef(getExprManager()); // keep ref to em in SWIG proxy class
  }
%typemap(javadestruct, methodname="delete", methodmodifiers="public synchronized") CVC4::Expr {
    SmtEngine.dlRef(em);
    em = null;
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        CVC4JNI.delete_Expr(swigCPtr);
      }
      swigCPtr = 0;
    }
  }
#endif /* SWIGJAVA */

%ignore CVC4::operator<<(std::ostream&, const Expr&);
%ignore CVC4::operator<<(std::ostream&, const TypeCheckingException&);

%ignore CVC4::expr::operator<<(std::ostream&, ExprSetDepth);
%ignore CVC4::expr::operator<<(std::ostream&, ExprPrintTypes);
%ignore CVC4::expr::operator<<(std::ostream&, ExprDag);
%ignore CVC4::expr::operator<<(std::ostream&, ExprSetLanguage);

%rename(assignInternal) CVC4::Expr::operator=(const Expr&);
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

#ifdef SWIGJAVA

// Instead of Expr::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::Expr::begin() const;
%ignore CVC4::Expr::end() const;
%extend CVC4::Expr {
  CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> iterator()
  {
    return CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr>(*$self);
  }
}

// Expr is "iterable" on the Java side
%typemap(javainterfaces) CVC4::Expr "java.lang.Iterable<edu.nyu.acsys.CVC4.Expr>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> "java.util.Iterator<edu.nyu.acsys.CVC4.Expr>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public edu.nyu.acsys.CVC4.Expr next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"
// getNext() just allows C++ iterator access from Java-side next(), make it private
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr>::getNext() "private";

#endif /* SWIGJAVA */

%include "expr/expr.h"

#ifdef SWIGPYTHON
/* The python bindings on Mac OS X have trouble with this one - leave it
 * out for now. */
//%template(getConstTypeConstant) CVC4::Expr::getConst<CVC4::TypeConstant>;
#else
%template(getConstTypeConstant) CVC4::Expr::getConst<CVC4::TypeConstant>;
#endif
%template(getConstArrayStoreAll) CVC4::Expr::getConst<CVC4::ArrayStoreAll>;
%template(getConstAscriptionType) CVC4::Expr::getConst<CVC4::AscriptionType>;
%template(getConstBitVector) CVC4::Expr::getConst<CVC4::BitVector>;
%template(getConstBitVectorBitOf) CVC4::Expr::getConst<CVC4::BitVectorBitOf>;
%template(getConstBitVectorExtract) CVC4::Expr::getConst<CVC4::BitVectorExtract>;
%template(getConstBitVectorRepeat) CVC4::Expr::getConst<CVC4::BitVectorRepeat>;
%template(getConstBitVectorRotateLeft) CVC4::Expr::getConst<CVC4::BitVectorRotateLeft>;
%template(getConstBitVectorRotateRight) CVC4::Expr::getConst<CVC4::BitVectorRotateRight>;
%template(getConstBitVectorSignExtend) CVC4::Expr::getConst<CVC4::BitVectorSignExtend>;
%template(getConstBitVectorSize) CVC4::Expr::getConst<CVC4::BitVectorSize>;
%template(getConstBitVectorZeroExtend) CVC4::Expr::getConst<CVC4::BitVectorZeroExtend>;
%template(getConstBoolean) CVC4::Expr::getConst<bool>;
%template(getConstDatatypeIndexConstant) CVC4::Expr::getConst<CVC4::DatatypeIndexConstant>;
%template(getConstEmptySet) CVC4::Expr::getConst<CVC4::EmptySet>;
%template(getConstFloatingPoint) CVC4::Expr::getConst<CVC4::FloatingPoint>;
%template(getConstKind) CVC4::Expr::getConst<CVC4::kind::Kind_t>;
%template(getConstRational) CVC4::Expr::getConst<CVC4::Rational>;
%template(getConstRoundingMode) CVC4::Expr::getConst<CVC4::RoundingMode>;
%template(getConstString) CVC4::Expr::getConst<CVC4::String>;
%template(getConstUninterpretedConstant) CVC4::Expr::getConst<CVC4::UninterpretedConstant>;

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"

%template(JavaIteratorAdapter_Expr) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr>;

#endif /* SWIGJAVA */

%include "expr/expr.h"
