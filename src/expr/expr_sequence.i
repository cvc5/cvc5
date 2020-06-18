%{
#include "expr/expr_sequence.h"
%}

#ifdef SWIGJAVA

%typemap(javabody) CVC4::ExprSequence %{
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

  public $javaclassname(ExprManager em, Type type, vectorExpr seq) {
    this(type, seq);
    this.em = em;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) ExprSequence {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::ExprSequence {
  this(null, $imcall, true);
}

%javamethodmodifiers CVC4::ExprSequence::ExprSequence(Type type, vectorExpr seq) "private";

#endif

%rename(equals) CVC4::ExprSequence::operator==(const ExprSequence&) const;
%ignore CVC4::ExprSequence::operator!=(const ExprSequence&) const;
%ignore CVC4::ExprSequence::getSequence() const;

%rename(less) CVC4::ExprSequence::operator<(const ExprSequence&) const;
%rename(lessEqual) CVC4::ExprSequence::operator<=(const ExprSequence&) const;
%rename(greater) CVC4::ExprSequence::operator>(const ExprSequence&) const;
%rename(greaterEqual) CVC4::ExprSequence::operator>=(const ExprSequence&) const;

%rename(apply) CVC4::ExprSequenceHashFunction::operator()(const ExprSequence&) const;

%ignore CVC4::operator<<(std::ostream& out, const ExprSequence& es);

%include "expr/expr_sequence.h"
