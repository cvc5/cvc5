%{
#include "bindings/java_iterator_adapter.h"
%}

#ifdef SWIGJAVA

%define SWIG_JAVA_ITERATOR_ADAPTER(TTYPE, VTYPE)

%typemap(javabody) CVC4::JavaIteratorAdapter %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  public $javaclassname(ExprManager em, $typemap(jstype, TTYPE) t) {
    this(t);
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) JavaIteratorAdapter<TTYPE, VTYPE> {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::JavaIteratorAdapter<TTYPE, VTYPE> {
  this(null, $imcall, true);
}

%feature("valuewrapper") CVC4::JavaIteratorAdapter<TTYPE, VTYPE>;

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<TTYPE, VTYPE> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter< TTYPE, VTYPE > "java.util.Iterator<$typemap(jstype, VTYPE)>";

// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<TTYPE, VTYPE> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public $typemap(jstype, VTYPE) next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"

// getNext() just allows C++ iterator access from Java-side next(), make it private
%javamethodmodifiers CVC4::JavaIteratorAdapter<TTYPE, VTYPE>::getNext() "private";

%javamethodmodifiers CVC4::JavaIteratorAdapter<TTYPE, VTYPE>::JavaIteratorAdapter(const TTYPE& t) "private";

%enddef

%include "bindings/java_iterator_adapter.h"

namespace CVC4 {
  template<class T, class V> class JavaIteratorAdapter {
    SWIG_JAVA_ITERATOR_ADAPTER(T, V)
  };
}

#endif
