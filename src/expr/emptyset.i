%{
#include "expr/emptyset.h"
%}

#ifdef SWIGJAVA

%typemap(javabody) CVC4::EmptySet %{
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

  public $javaclassname(ExprManager em, SetType t) {
    this(t);
    this.em = em;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) EmptySet {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::EmptySet {
  this(null, $imcall, true);
}

%javamethodmodifiers CVC4::EmptySet::EmptySet(Type t) "private";

%typemap(javaout) const CVC4::SetType& {
  return new SetType(this.em, $jnicall, false);
}

#endif

%ignore CVC4::EmptySet::EmptySet(const CVC4::EmptySet& other);

%rename(equals) CVC4::EmptySet::operator==(const EmptySet&) const;
%ignore CVC4::EmptySet::operator!=(const EmptySet&) const;

%rename(less) CVC4::EmptySet::operator<(const EmptySet&) const;
%rename(lessEqual) CVC4::EmptySet::operator<=(const EmptySet&) const;
%rename(greater) CVC4::EmptySet::operator>(const EmptySet&) const;
%rename(greaterEqual) CVC4::EmptySet::operator>=(const EmptySet&) const;

%rename(apply) CVC4::EmptySetHashFunction::operator()(const EmptySet&) const;

%ignore CVC4::operator<<(std::ostream& out, const EmptySet& es);

%include "expr/emptyset.h"
