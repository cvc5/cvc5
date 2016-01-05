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
  CVC4::JavaIteratorAdapter<CVC4::UnsatCore> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::UnsatCore>(*$self);
  }
}

// UnsatCore is "iterable" on the Java side
%typemap(javainterfaces) CVC4::UnsatCore "java.lang.Iterable<edu.nyu.acsys.CVC4.Expr>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::UnsatCore> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::UnsatCore> "java.util.Iterator<edu.nyu.acsys.CVC4.Expr>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::UnsatCore> "
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
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::UnsatCore>::getNext() "private";

// map the types appropriately
%typemap(jni) CVC4::UnsatCore::const_iterator::value_type "jobject";
%typemap(jtype) CVC4::UnsatCore::const_iterator::value_type "edu.nyu.acsys.CVC4.Expr";
%typemap(jstype) CVC4::UnsatCore::const_iterator::value_type "edu.nyu.acsys.CVC4.Expr";
%typemap(javaout) CVC4::UnsatCore::const_iterator::value_type { return $jnicall; }

#endif /* SWIGJAVA */

%include "proof/unsat_core.h"

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"

%template(JavaIteratorAdapter_UnsatCore) CVC4::JavaIteratorAdapter<CVC4::UnsatCore>;

#endif /* SWIGJAVA */
