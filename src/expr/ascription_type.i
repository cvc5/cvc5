%{
#include "expr/ascription_type.h"
%}

#ifdef SWIGJAVA

%typemap(javabody) CVC4::AscriptionType %{
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

  public $javaclassname(ExprManager em, Type t) {
    this(t);
    this.em = em;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) AscriptionType {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::AscriptionType {
  this(null, $imcall, true);
}

%javamethodmodifiers CVC4::AscriptionType::AscriptionType(Type t) "private";

#endif

%rename(equals) CVC4::AscriptionType::operator==(const AscriptionType&) const;
%ignore CVC4::AscriptionType::operator!=(const AscriptionType&) const;

%rename(apply) CVC4::AscriptionTypeHashFunction::operator()(const AscriptionType&) const;

%ignore CVC4::operator<<(std::ostream&, AscriptionType);

%include "expr/ascription_type.h"
