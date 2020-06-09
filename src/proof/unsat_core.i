%{
#include "proof/unsat_core.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

#endif /* SWIGJAVA */
%}

%ignore CVC4::operator<<(std::ostream&, const UnsatCore&);

#ifdef SWIGJAVA

// Instead of UnsatCore::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::UnsatCore::begin();
%ignore CVC4::UnsatCore::end();
%ignore CVC4::UnsatCore::begin() const;
%ignore CVC4::UnsatCore::end() const;
%extend CVC4::UnsatCore {
  CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr> iterator()
  {
    return CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr>(*$self);
  }

  std::string toString()
  {
    std::stringstream ss;
    ss << (*$self);
    return ss.str();
  }
}

// UnsatCore is "iterable" on the Java side
%typemap(javainterfaces) CVC4::UnsatCore "java.lang.Iterable<edu.stanford.CVC4.Expr>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr> "java.util.Iterator<edu.stanford.CVC4.Expr>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr> "
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
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr>::getNext() "private";

#endif /* SWIGJAVA */

%include "proof/unsat_core.h"

#ifdef SWIGJAVA

%include <std_vector.i>

%include "bindings/java_iterator_adapter.h"

%template(JavaIteratorAdapter_UnsatCore) CVC4::JavaIteratorAdapter<CVC4::UnsatCore, CVC4::Expr>;

#endif /* SWIGJAVA */
