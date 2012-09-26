#include "JniUtils.h"

// for CVC4: removed; don't need these
//#include <typecheck_exception.h>
//#include <sound_exception.h>
//#include <eval_exception.h>
//#include <command_line_exception.h>
//#include <parser_exception.h>
//#include <smtlib_exception.h>

// for CVC4: need these for compatibility layer
#include "compat/cvc3_compat.h"
#include "Embedded.h"

using namespace std;
using namespace CVC3;

namespace Java_cvc3_JniUtils {

  /// Embedding of c++ objects in java objects

  Embedded* unembed(JNIEnv* env, jobject jobj) {
    Embedded* embedded = (Embedded*) env->GetDirectBufferAddress(jobj);
    DebugAssert(embedded != NULL, "JniUtils::unembed: embedded object is NULL");
    return embedded;
  }

  void deleteEmbedded(JNIEnv* env, jobject jobj) {
    Embedded* embedded = unembed(env, jobj);
    DebugAssert(embedded != NULL, "JniUtils::deleteEmbedded: embedded object is NULL");
    delete embedded;
  }



  /// Conversions between c++ and java

  bool toCpp(jboolean j) {
    return (bool)j;
  }

  jstring toJava(JNIEnv* env, const string& cstring) {
    return env->NewStringUTF(cstring.c_str());
  }
  
  jstring toJava(JNIEnv* env, const char* cstring) {
    return env->NewStringUTF(cstring);
  }

  string toCpp(JNIEnv* env, const jstring& jstring) {
    const char* cstring = env->GetStringUTFChars(jstring, NULL);
    string string(cstring);
    env->ReleaseStringUTFChars(jstring, cstring);
    return string;
  }
  
  jstring toJava(JNIEnv* env, CVC3::QueryResult result) {
    switch (result) {
    case SATISFIABLE: return toJava(env, "SATISFIABLE");
    case UNSATISFIABLE: return toJava(env, "UNSATISFIABLE");
    case ABORT: return toJava(env, "ABORT");
    case UNKNOWN: return toJava(env, "UNKNOWN");
    }
    
    DebugAssert(false, "JniUtils::toJava(QueryResult): unreachable");
    return toJava(env, ""); // to avoid compiler warning
  }

  jstring toJava(JNIEnv* env, CVC3::FormulaValue result) {
    switch (result) {
    case TRUE_VAL: return toJava(env, "TRUE_VAL");
    case FALSE_VAL: return toJava(env, "FALSE_VAL");
    case UNKNOWN_VAL: return toJava(env, "UNKNOWN_VAL");
    }
    
    DebugAssert(false, "JniUtils::toJava(FormulaValue): unreachable");
    return toJava(env, "UNDEFINED");
  }

  jstring toJava(JNIEnv* env, CVC3::InputLanguage lang) {
    switch (lang) {
    case PRESENTATION_LANG: return toJava(env, "PRESENTATION");
    case SMTLIB_LANG: return toJava(env, "SMTLIB");
    case SMTLIB_V2_LANG: return toJava(env, "SMTLIB_V2");
    //case LISP_LANG: return toJava(env, "LISP");
    default: /* fall through */;
    }
    
    DebugAssert(false, "JniUtils::toJava(InputLanguage): unreachable");
    return toJava(env, "UNDEFINED");
  }

  InputLanguage toCppInputLanguage(JNIEnv* env, const string& lang) {
    if (lang.compare("PRESENTATION") == 0) {
      return PRESENTATION_LANG;
    } else if (lang.compare("SMTLIB") == 0) {
      return SMTLIB_LANG;
    } else if (lang.compare("SMTLIB_V2") == 0) {
      return SMTLIB_V2_LANG;
    /*
    } else if (lang.compare("LISP") == 0) {
      return LISP_LANG;
    */
    }
    
    DebugAssert(false, "JniUtils::toCpp(InputLanguage): unreachable");
    return CVC4::language::input::LANG_MAX;
  }

  void toJava(JNIEnv* env, const Exception& e) {
    /* for CVC4: don't worry about legacy exception mapping
    string exceptionName("cvc3/");
    if (dynamic_cast<const TypecheckException*>(&e) != NULL) {
      exceptionName += "TypecheckException";
    } else if (dynamic_cast<const CVC3::SoundException*>(&e) != NULL) {
      exceptionName += "SoundException";
    } else if (dynamic_cast<const CVC3::EvalException*>(&e) != NULL) {
      exceptionName += "EvalException";
    } else if (dynamic_cast<const CVC3::CLException*>(&e) != NULL) {
      exceptionName += "CLException";
    } else if (dynamic_cast<const CVC3::ParserException*>(&e) != NULL) {
      exceptionName += "ParserException";
    } else if (dynamic_cast<const CVC3::SmtlibException*>(&e) != NULL) {
      exceptionName += "SmtlibException";
    } else if (dynamic_cast<const CVC3::DebugException*>(&e) != NULL) {
      exceptionName += "DebugException";
    } else {
      exceptionName += "Cvc3Exception";
    }
    */

    jclass exceptionClass = env->FindClass("java/lang/RuntimeException");
    // queues up the exception in the Java layer
    env->ThrowNew(exceptionClass, e.toString().c_str());
  }


  vector<string> toCppV(JNIEnv* env, const jobjectArray& jarray) {
    vector<string> v;
    int length = env->GetArrayLength(jarray);
    for (int i = 0; i < length; ++i) {
      v.push_back(toCpp(env, (jstring)env->GetObjectArrayElement(jarray, i)));
    }
    return v;
  }

  vector<vector<string> > toCppVV(JNIEnv* env, const jobjectArray& jarray) {
    vector<vector<string> > v;
    int length = env->GetArrayLength(jarray);
    for (int i = 0; i < length; ++i) {
      jobjectArray jsub = static_cast<jobjectArray>(env->GetObjectArrayElement(jarray, i));
      v.push_back(toCppV(env, jsub));
    }
    return v;
  }

  vector<vector<vector<string> > > toCppVVV(JNIEnv* env, const jobjectArray& jarray) {
    vector<vector<vector<string> > > v;
    int length = env->GetArrayLength(jarray);
    for (int i = 0; i < length; ++i) {
      jobjectArray jsub = static_cast<jobjectArray>(env->GetObjectArrayElement(jarray, i));
      v.push_back(toCppVV(env, jsub));
    }
    return v;
  }

  jobjectArray toJavaV(JNIEnv* env, const vector<string>& v) {
    jobjectArray jarray = (jobjectArray)
      env->NewObjectArray(
	v.size(),
	env->FindClass("java/lang/String"),
	env->NewStringUTF(""));

    for(unsigned i = 0; i < v.size(); ++i) {
      env->SetObjectArrayElement(jarray, i, toJava(env, v[i]));
    }

    return jarray;
  }


  vector<bool> toCppV(JNIEnv* env, const jbooleanArray& jarray) {
    int length = env->GetArrayLength(jarray);
    jboolean* jboolean = env->GetBooleanArrayElements(jarray, NULL);

    vector<bool> v;
    for (int i = 0; i < length; ++i) {
      v.push_back(jboolean[i]);
    }
    env->ReleaseBooleanArrayElements(jarray, jboolean, JNI_ABORT);
    
    return v;
  }
}
