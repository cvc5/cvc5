%{
#include "expr/expr.h"
%}

%ignore CVC4::Expr::Expr(const Expr&);
// This is currently the only function that would require bindings for
// `std::unordered_map<Expr, Expr, ExprHashFunction>` and is better implemented
// at the Java/Python level if needed. Thus, we ignore it here.
%ignore CVC4::Expr::substitute(const std::unordered_map<Expr, Expr, ExprHashFunction> map) const;
%ignore CVC4::operator<<(std::ostream&, const Expr&);
%ignore CVC4::operator<<(std::ostream&, const TypeCheckingException&);
// Ignore because we would not know which ExprManager the Expr belongs to
%ignore CVC4::TypeCheckingException::getExpression() const;
%ignore CVC4::expr::operator<<(std::ostream&, ExprSetDepth);
%ignore CVC4::expr::operator<<(std::ostream&, ExprPrintTypes);
%ignore CVC4::expr::operator<<(std::ostream&, ExprDag);
%ignore CVC4::expr::operator<<(std::ostream&, ExprSetLanguage);
%ignore CVC4::Expr::operator=(const Expr&);
%ignore CVC4::Expr::operator!=(const Expr&) const;
%ignore CVC4::Expr::operator bool() const;// can just use isNull()

%rename(equals) CVC4::Expr::operator==(const Expr&) const;
%rename(less) CVC4::Expr::operator<(const Expr&) const;
%rename(lessEqual) CVC4::Expr::operator<=(const Expr&) const;
%rename(greater) CVC4::Expr::operator>(const Expr&) const;
%rename(greaterEqual) CVC4::Expr::operator>=(const Expr&) const;

%rename(getChild) CVC4::Expr::operator[](unsigned i) const;

#ifdef SWIGJAVA

// For the Java bindings, we implement `getExprManager()` at the Java level
// because we can't map back the C++ point to the Java object
%ignore CVC4::Expr::getExprManager() const;
%rename(apply) CVC4::ExprHashFunction::operator()(CVC4::Expr) const;

%typemap(javabody) CVC4::Expr %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em; // keep ref to em in SWIG proxy class
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  public ExprManager getExprManager() throws edu.stanford.CVC4.Exception {
    return this.em;
  }

  public JavaIteratorAdapter_Expr iterator() {
    return new JavaIteratorAdapter_Expr(this.em, this);
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) Expr {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::Expr {
  this(null, $imcall, true);
}

%typemap(javaout) CVC4::Expr {
  return new Expr(this.em, $jnicall, true);
}

SWIG_STD_VECTOR_EM(CVC4::Expr, const CVC4::Expr&)
SWIG_STD_VECTOR_EM(std::vector<CVC4::Expr>, const std::vector<CVC4::Expr>&)

%template(vectorExpr) std::vector<CVC4::Expr>;
%typemap(javaout) std::vector<CVC4::Expr> {
  return new vectorExpr(this.em, $jnicall, true);
}
%typemap(javaout) const std::vector<CVC4::Expr>& {
  return new vectorExpr(this.em, $jnicall, false);
}
%template(vectorVectorExpr) std::vector<std::vector<CVC4::Expr>>;

%javamethodmodifiers CVC4::Expr::operator=(const Expr&) "protected";

%typemap(javaout) const CVC4::AscriptionType& {
  return new AscriptionType(this.em, $jnicall, $owner);
}

%typemap(javaout) const CVC4::EmptySet& {
  return new EmptySet(this.em, $jnicall, $owner);
}

%typemap(javaout) const CVC4::ExprSequence& {
  return new ExprSequence(this.em, $jnicall, $owner);
}

// Instead of Expr::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::Expr::begin() const;
%ignore CVC4::Expr::end() const;
%ignore CVC4::Expr::const_iterator;

// Expr is "iterable" on the Java side
%typemap(javainterfaces) CVC4::Expr "java.lang.Iterable<edu.stanford.CVC4.Expr>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> "java.util.Iterator<edu.stanford.CVC4.Expr>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public edu.stanford.CVC4.Expr next() {
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

#ifdef SWIGPYTHON
%rename(doApply) CVC4::ExprHashFunction::operator()(CVC4::Expr) const;
#endif /* SWIGPYTHON */

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
%template(getConstExprSequence) CVC4::Expr::getConst<CVC4::ExprSequence>;
%template(getConstFloatingPoint) CVC4::Expr::getConst<CVC4::FloatingPoint>;
%template(getConstKind) CVC4::Expr::getConst<CVC4::kind::Kind_t>;
%template(getConstRational) CVC4::Expr::getConst<CVC4::Rational>;
%template(getConstRoundingMode) CVC4::Expr::getConst<CVC4::RoundingMode>;
%template(getConstString) CVC4::Expr::getConst<CVC4::String>;
%template(getConstUninterpretedConstant) CVC4::Expr::getConst<CVC4::UninterpretedConstant>;

#ifdef SWIGJAVA

SWIG_JAVA_ITERATOR_ADAPTER(CVC4::Expr, CVC4::Expr)
%template(JavaIteratorAdapter_Expr) CVC4::JavaIteratorAdapter<CVC4::Expr, CVC4::Expr>;

#endif /* SWIGJAVA */
