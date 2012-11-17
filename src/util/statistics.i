%{
#include "util/statistics.h"
#include "bindings/java_iterator_adapter.h"
#include "bindings/java_output_stream_adapter.h"
%}

%rename(assign) CVC4::Statistics::operator=(const StatisticsBase&);
%rename(assign) CVC4::Statistics::operator=(const Statistics& stats);

%ignore CVC4::StatisticsBase::begin();
%ignore CVC4::StatisticsBase::end();
%ignore CVC4::StatisticsBase::begin() const;
%ignore CVC4::StatisticsBase::end() const;
%extend CVC4::StatisticsBase {
  CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::StatisticsBase>(*$self);
  }
}

%typemap(javainterfaces) CVC4::StatisticsBase "java.lang.Iterable<Object>";

%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> "java.util.Iterator";
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase> "
  public void remove() {
    throw new java.lang.UnsupportedOperationException();
  }

  public Object next() {
    if(hasNext()) {
      return getNext();
    } else {
      throw new java.util.NoSuchElementException();
    }
  }
"

%typemap(jni) CVC4::StatisticsBase::const_iterator::value_type "jobjectArray";
%typemap(jtype) CVC4::StatisticsBase::const_iterator::value_type "java.lang.Object[]";
%typemap(jstype) CVC4::StatisticsBase::const_iterator::value_type "java.lang.Object[]";
%typemap(javaout) CVC4::StatisticsBase::const_iterator::value_type { return $jnicall; }
%typemap(out) CVC4::StatisticsBase::const_iterator::value_type {
      $result = jenv->NewObjectArray(2, jenv->FindClass("java/lang/Object"), $null);
      jenv->SetObjectArrayElement($result, 0, jenv->NewStringUTF($1.first.c_str()));
      jclass clazz = jenv->FindClass("edu/nyu/acsys/CVC4/SExpr");
      jmethodID methodid = jenv->GetMethodID(clazz, "<init>", "(JZ)V");
      jenv->SetObjectArrayElement($result, 1, jenv->NewObject(jenv->FindClass("edu/nyu/acsys/CVC4/SExpr"), methodid, reinterpret_cast<long>(new CVC4::SExpr($1.second)), true));
    };

%include "util/statistics.h"
%include "bindings/java_iterator_adapter.h"
%include "bindings/java_output_stream_adapter.h"

%template(JavaIteratorAdapter_StatisticsBase) CVC4::JavaIteratorAdapter<CVC4::StatisticsBase>;
