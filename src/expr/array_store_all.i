%{
#include "expr/array_store_all.h"
%}

#ifdef SWIGJAVA

%typemap(javabody) CVC4::ArrayStoreAll %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  public $javaclassname(ExprManager em, ArrayType type, Expr expr) {
    this(type, expr);
    this.em = em;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) ArrayStoreAll {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::ArrayStoreAll {
  this(null, $imcall, true);
}

%typemap(javaout) const CVC4::Expr& {
  return new Expr(this.em, $jnicall, false);
}

%typemap(javaout) const CVC4::ArrayType& {
  return new ArrayType(this.em, $jnicall, false);
}

%typemap(javaout) const CVC4::ArrayStoreAll& {
  return new ArrayStoreAll(this.em, $jnicall, false);
}

%javamethodmodifiers CVC4::ArrayStoreAll::ArrayStoreAll(const ArrayType& type, const Expr& expr) "private";

#endif /* SWIGJAVA */

%ignore CVC4::ArrayStoreAll::ArrayStoreAll(const ArrayStoreAll& other);
%rename(equals) CVC4::ArrayStoreAll::operator==(const ArrayStoreAll&) const;
%ignore CVC4::ArrayStoreAll::operator!=(const ArrayStoreAll&) const;
%ignore CVC4::ArrayStoreAll::operator=(const ArrayStoreAll&);
%rename(less) CVC4::ArrayStoreAll::operator<(const ArrayStoreAll&) const;
%rename(lessEqual) CVC4::ArrayStoreAll::operator<=(const ArrayStoreAll&) const;
%rename(greater) CVC4::ArrayStoreAll::operator>(const ArrayStoreAll&) const;
%rename(greaterEqual) CVC4::ArrayStoreAll::operator>=(const ArrayStoreAll&) const;
%rename(apply) CVC4::ArrayStoreAllHashFunction::operator()(const ArrayStoreAll&) const;
%ignore CVC4::operator<<(std::ostream&, const ArrayStoreAll&);

%include "expr/type.i"
%include "expr/array_store_all.h"
