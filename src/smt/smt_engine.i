%{
#include "smt/smt_engine.h"
%}

#ifdef SWIGJAVA
%typemap(javacode) CVC4::SmtEngine %{
  // a ref is kept here to keep Java GC from collecting the EM
  // before the SmtEngine
  private Object emRef;
  static final native Object mkRef(Object obj);
  static final native void dlRef(Object obj);
%}
%native (mkRef) jobject SmtEngine::mkRef(jobject);
%native (dlRef) void SmtEngine::dlRef(jobject);
%{
extern "C" {
SWIGEXPORT jobject JNICALL Java_edu_nyu_acsys_CVC4_SmtEngine_mkRef(JNIEnv* jenv, jclass jcls, jobject o) {
  if(o == NULL) {
    return NULL;
  }
  return jenv->NewGlobalRef(o);
}
SWIGEXPORT void JNICALL Java_edu_nyu_acsys_CVC4_SmtEngine_dlRef(JNIEnv* jenv, jclass jcls, jobject o) {
  if(o != NULL) {
    jenv->DeleteGlobalRef(o);
  }
}
}
%}
%typemap(javaconstruct) SmtEngine {
    this($imcall, true);
    emRef = mkRef(em); // keep ref to expr manager in SWIG proxy class
  }
%typemap(javadestruct, methodname="delete", methodmodifiers="public synchronized") CVC4::SmtEngine {
    dlRef(emRef);
    emRef = null;
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        CVC4JNI.delete_SmtEngine(swigCPtr);
      }
      swigCPtr = 0;
    }
  }
#endif // SWIGJAVA

%ignore CVC4::SmtEngine::setLogic(const char*);
%ignore CVC4::smt::currentProofManager();

%include "smt/smt_engine.h"
