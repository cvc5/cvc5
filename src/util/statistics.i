%{
#include "util/statistics.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

#endif /* SWIGJAVA */
%}

%rename(assign) CVC4::Statistics::operator=(const StatisticsBase&);
%rename(assign) CVC4::Statistics::operator=(const Statistics& stats);

#ifdef SWIGJAVA

// Instead of StatisticsBase::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::StatisticsBase::begin();
%ignore CVC4::StatisticsBase::end();
%ignore CVC4::StatisticsBase::begin() const;
%ignore CVC4::StatisticsBase::end() const;
%extend CVC4::StatisticsBase {
  CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::StatisticsBase>(*$self);
  }
}

// StatisticsBase is "iterable" on the Java side
%typemap(javainterfaces) CVC4::StatisticsBase "java.lang.Iterable<Object[]>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> "java.util.Iterator<Object[]>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public Object[] next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"
// getNext() just allows C++ iterator access from Java-side next(), make it private
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::StatisticsBase>::getNext() "private";

// map the types appropriately.  for statistics, the "payload" of the iterator is an Object[].
// These Object arrays are always of two elements, the first is a String and the second an
// SExpr.  (On the C++ side, it is a std::pair<std::string, SExpr>.)
%typemap(jni) CVC4::StatisticsBase::const_iterator::value_type "jobjectArray";
%typemap(jtype) CVC4::StatisticsBase::const_iterator::value_type "java.lang.Object[]";
%typemap(jstype) CVC4::StatisticsBase::const_iterator::value_type "java.lang.Object[]";
%typemap(javaout) CVC4::StatisticsBase::const_iterator::value_type { return $jnicall; }
%typemap(out) CVC4::StatisticsBase::const_iterator::value_type {
      $result = jenv->NewObjectArray(2, jenv->FindClass("java/lang/Object"), $null);
      jenv->SetObjectArrayElement($result, 0, jenv->NewStringUTF($1.first.c_str()));
      jclass clazz = jenv->FindClass("edu/nyu/acsys/CVC4/SExpr");
      jmethodID methodid = jenv->GetMethodID(clazz, "<init>", "(JZ)V");
      jenv->SetObjectArrayElement($result, 1, jenv->NewObject(clazz, methodid, reinterpret_cast<long>(new CVC4::SExpr($1.second)), true));
    };

#endif /* SWIGJAVA */

%include "util/statistics.h"

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"

%template(JavaIteratorAdapter_StatisticsBase) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase>;

#endif /* SWIGJAVA */
