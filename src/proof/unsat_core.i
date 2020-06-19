%{
#include "proof/unsat_core.h"
%}

%ignore CVC4::operator<<(std::ostream&, const UnsatCore&);

#ifdef SWIGJAVA

%typemap(javabody) CVC4::UnsatCore %{
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

  public JavaIteratorAdapter_UnsatCore iterator() {
    return new JavaIteratorAdapter_UnsatCore(this.em, this);
  }
%}

%typemap(javaout) CVC4::Expr {
  return new Expr(this.em, $jnicall, true);
}

%ignore CVC4::UnsatCore::UnsatCore();
%ignore CVC4::UnsatCore::UnsatCore(SmtEngine* smt, std::vector<Expr> core);

// Instead of UnsatCore::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::UnsatCore::begin();
%ignore CVC4::UnsatCore::end();
%ignore CVC4::UnsatCore::begin() const;
%ignore CVC4::UnsatCore::end() const;

%extend CVC4::UnsatCore {
  std::string toString()
  {
    std::stringstream ss;
    ss << (*$self);
    return ss.str();
  }
}

// UnsatCore is "iterable" on the Java side
%typemap(javainterfaces) CVC4::UnsatCore "java.lang.Iterable<edu.stanford.CVC4.Expr>";

#endif /* SWIGJAVA */

%include "proof/unsat_core.h"

#ifdef SWIGJAVA

SWIG_JAVA_ITERATOR_ADAPTER(CVC4::UnsatCore, CVC4::Expr)
%template(JavaIteratorAdapter_UnsatCore) CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr>;

#endif /* SWIGJAVA */
