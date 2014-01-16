%{
#include "util/record.h"

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

// Instead of Record::begin() and end(), create an
// iterator() method on the Java side that returns a Java-style
// Iterator.
%ignore CVC4::Record::begin() const;
%ignore CVC4::Record::end() const;
%extend CVC4::Record {
  CVC4::Type find(std::string name) const {
    CVC4::Record::const_iterator i;
    for(i = $self->begin(); i != $self->end(); ++i) {
      if((*i).first == name) {
        return (*i).second;
      }
    }
    return CVC4::Type();
  }

  CVC4::JavaIteratorAdapter<CVC4::Record> iterator() {
    return CVC4::JavaIteratorAdapter<CVC4::Record>(*$self);
  }
}

// Record is "iterable" on the Java side
%typemap(javainterfaces) CVC4::Record "java.lang.Iterable<Object[]>";

// the JavaIteratorAdapter should not be public, and implements Iterator
%typemap(javaclassmodifiers) CVC4::JavaIteratorAdapter<CVC4::Record> "class";
%typemap(javainterfaces) CVC4::JavaIteratorAdapter<CVC4::Record> "java.util.Iterator<Object[]>";
// add some functions to the Java side (do it here because there's no way to do these in C++)
%typemap(javacode) CVC4::JavaIteratorAdapter<CVC4::Record> "
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
%javamethodmodifiers CVC4::JavaIteratorAdapter<CVC4::Record>::getNext() "private";

// map the types appropriately.  for records, the "payload" of the iterator is an Object[].
// These Object arrays are always of two elements, the first is a String and the second a
// Type.  (On the C++ side, it is a std::pair<std::string, SExpr>.)
%typemap(jni) CVC4::Record::const_iterator::value_type = std::pair<std::string, CVC4::Type>;
%typemap(jtype) CVC4::Record::const_iterator::value_type = std::pair<std::string, CVC4::Type>;
%typemap(jstype) CVC4::Record::const_iterator::value_type = std::pair<std::string, CVC4::Type>;
%typemap(javaout) CVC4::Record::const_iterator::value_type = std::pair<std::string, CVC4::Type>;
%typemap(out) CVC4::Record::const_iterator::value_type = std::pair<std::string, CVC4::Type>;

#endif /* SWIGJAVA */

%include "util/record.h"

#ifdef SWIGJAVA

%include "bindings/java_iterator_adapter.h"
%include "bindings/java_stream_adapters.h"

%template(JavaIteratorAdapter_Record) CVC4::JavaIteratorAdapter<CVC4::Record>;

#endif /* SWIGJAVA */
