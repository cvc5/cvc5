/*********************                                                        */
/*! \file java_stream_adapters.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An OutputStream adapter for the Java bindings
 **
 ** An OutputStream adapter for the Java bindings.  This works with a lot
 ** of help from SWIG, and custom typemaps in the ".i" SWIG interface files
 ** for CVC4.  The basic idea is that, when a CVC4 function with a
 ** std::ostream& parameter is called, a Java-side binding is generated
 ** taking a java.io.OutputStream.  Now, the problem is that std::ostream
 ** has no Java equivalent, and java.io.OutputStream has no C++ equivalent,
 ** so we use this class (which exists on both sides) as the go-between.
 ** The wrapper connecting the Java function (taking an OutputStream) and
 ** the C++ function (taking an ostream) creates a JavaOutputStreamAdapter,
 ** and call the C++ function with the stringstream inside.  After the call,
 ** the generated stream material is collected and output to the Java-side
 ** OutputStream.
 **/

// private to the bindings layer
#ifndef SWIGJAVA
#  error This should only be included from the Java bindings layer.
#endif /* SWIGJAVA */

#include <sstream>
#include <set>
#include <cassert>
#include <iosfwd>
#include <string>
#include <jni.h>

#ifndef CVC4__BINDINGS__JAVA_STREAM_ADAPTERS_H
#define CVC4__BINDINGS__JAVA_STREAM_ADAPTERS_H

namespace CVC4 {

class JavaOutputStreamAdapter : public std::ostringstream {
public:
  std::string toString() { return str(); }
};/* class JavaOutputStreamAdapter */

class JavaInputStreamAdapter : public std::stringstream {
  static std::set<JavaInputStreamAdapter*> s_adapters;
  jobject inputStream;

  JavaInputStreamAdapter& operator=(const JavaInputStreamAdapter&);
  JavaInputStreamAdapter(const JavaInputStreamAdapter&);

public:
  JavaInputStreamAdapter(jobject inputStream) : inputStream(inputStream) {
    s_adapters.insert(this);
  }

  ~JavaInputStreamAdapter() {
    s_adapters.erase(this);
  }

  static void pullAdapters(JNIEnv* jenv) {
    for(std::set<JavaInputStreamAdapter*>::iterator i = s_adapters.begin();
        i != s_adapters.end();
        ++i) {
      (*i)->pull(jenv);
    }
  }

  jobject getInputStream() const {
    return inputStream;
  }

  void pull(JNIEnv* jenv) {
    if(fail() || eof()) {
      clear();
    }
    jclass clazz = jenv->FindClass("java/io/InputStream");
    assert(clazz != NULL && jenv->ExceptionOccurred() == NULL);
    jmethodID method = jenv->GetMethodID(clazz, "available", "()I");
    assert(method != NULL && jenv->ExceptionOccurred() == NULL);
    jint available = jenv->CallIntMethod(inputStream, method);
    assert(jenv->ExceptionOccurred() == NULL);
    jbyteArray bytes = jenv->NewByteArray(available);
    assert(bytes != NULL && jenv->ExceptionOccurred() == NULL);
    method = jenv->GetMethodID(clazz, "read", "([B)I");
    assert(method != NULL && jenv->ExceptionOccurred() == NULL);
    jint nread = jenv->CallIntMethod(inputStream, method, bytes);
    assert(jenv->ExceptionOccurred() == NULL);
    jbyte* bptr = jenv->GetByteArrayElements(bytes, NULL);
    assert(jenv->ExceptionOccurred() == NULL);
    std::copy(bptr, bptr + nread, std::ostream_iterator<char>(*this));
    *this << std::flush;
    jenv->ReleaseByteArrayElements(bytes, bptr, 0);
    assert(jenv->ExceptionOccurred() == NULL);
    assert(good());
    assert(!eof());
  }

};/* class JavaInputStreamAdapter */

}/* CVC4 namespace */

#endif /* CVC4__BINDINGS__JAVA_STREAM_ADAPTERS_H */
