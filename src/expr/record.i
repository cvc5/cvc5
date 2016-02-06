%{
#include "expr/record.h"

#ifdef SWIGJAVA

#include "bindings/java_iterator_adapter.h"
#include "bindings/java_stream_adapters.h"

#endif /* SWIGJAVA */
%}

%rename(equals) CVC4::RecordSelect::operator==(const RecordSelect&) const;
%ignore CVC4::RecordSelect::operator!=(const RecordSelect&) const;

%rename(equals) CVC4::RecordUpdate::operator==(const RecordUpdate&) const;
%ignore CVC4::RecordUpdate::operator!=(const RecordUpdate&) const;

%rename(equals) CVC4::Record::operator==(const Record&) const;
%ignore CVC4::Record::operator!=(const Record&) const;
%rename(getField) CVC4::Record::operator[](size_t) const;

%rename(apply) CVC4::RecordHashFunction::operator()(const Record&) const;
%rename(apply) CVC4::RecordSelectHashFunction::operator()(const RecordSelect&) const;
%rename(apply) CVC4::RecordUpdateHashFunction::operator()(const RecordUpdate&) const;

%ignore CVC4::operator<<(std::ostream&, const Record&);
%ignore CVC4::operator<<(std::ostream&, const RecordSelect&);
%ignore CVC4::operator<<(std::ostream&, const RecordUpdate&);

#ifdef SWIGJAVA

// These Object arrays are always of two elements, the first is a String and the second a
// Type.  (On the C++ side, it is a std::pair<std::string, Type>.)
%typemap(jni) std::pair<std::string, CVC4::Type> "jobjectArray";
%typemap(jtype) std::pair<std::string, CVC4::Type> "java.lang.Object[]";
%typemap(jstype) std::pair<std::string, CVC4::Type> "java.lang.Object[]";
%typemap(javaout) std::pair<std::string, CVC4::Type> { return $jnicall; }
%typemap(out) std::pair<std::string, CVC4::Type> {
      $result = jenv->NewObjectArray(2, jenv->FindClass("java/lang/Object"), $null);
      jenv->SetObjectArrayElement($result, 0, jenv->NewStringUTF($1.first.c_str()));
      jclass clazz = jenv->FindClass("edu/nyu/acsys/CVC4/Type");
      jmethodID methodid = jenv->GetMethodID(clazz, "<init>", "(JZ)V");
      jenv->SetObjectArrayElement($result, 1, jenv->NewObject(clazz, methodid, reinterpret_cast<long>(new CVC4::Type($1.second)), true));
    };



#endif /* SWIGJAVA */

%include "expr/record.h"

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"


#endif /* SWIGJAVA */
