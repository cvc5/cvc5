%{
#include "expr/type.h"
%}

#ifdef SWIGPYTHON
%rename(doApply) CVC4::TypeHashFunction::operator()(const CVC4::Type&) const;
#else /* SWIGPYTHON */
%rename(apply) CVC4::TypeHashFunction::operator()(const CVC4::Type&) const;
#endif /* SWIGPYTHON */

#ifdef SWIGJAVA
%typemap(javabody) CVC4::Type %{
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
%javamethodmodifiers CVC4::Type::operator=(const Type&) "protected";
%typemap(javacode) CVC4::Type %{
  // a ref is kept here to keep Java GC from collecting the ExprManager
  // before the Type
  private Object em;

  public Type assign(Type t) {
    Type r = assignInternal(t);
    this.em = SmtEngine.mkRef(getExprManager()); // keep ref to em in SWIG proxy class
    return r;
  }
%}
%typemap(javaconstruct) Type {
    this($imcall, true);
    this.em = SmtEngine.mkRef(getExprManager()); // keep ref to em in SWIG proxy class
  }
%typemap(javadestruct, methodname="delete", methodmodifiers="public synchronized") CVC4::Type {
    SmtEngine.dlRef(em);
    em = null;
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        CVC4JNI.delete_Type(swigCPtr);
      }
      swigCPtr = 0;
    }
  }
#endif /* SWIGJAVA */
%ignore CVC4::operator<<(std::ostream&, const Type&);

%rename(assignInternal) CVC4::Type::operator=(const Type&);
%rename(equals) CVC4::Type::operator==(const Type&) const;
%ignore CVC4::Type::operator!=(const Type&) const;
%rename(less) CVC4::Type::operator<(const Type&) const;
%rename(lessEqual) CVC4::Type::operator<=(const Type&) const;
%rename(greater) CVC4::Type::operator>(const Type&) const;
%rename(greaterEqual) CVC4::Type::operator>=(const Type&) const;

namespace CVC4 {
  namespace expr {
    %ignore exportTypeInternal;
  }/* CVC4::expr namespace */
}/* CVC4 namespace */

%include "expr/type.h"
