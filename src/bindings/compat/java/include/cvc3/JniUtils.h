#ifndef _java__cvc3__jni_utils_h_
#define _java__cvc3__jni_utils_h_

#include <cassert>
#include <string>
#include <jni.h>
#include <typeinfo>
#include "compat/cvc3_compat.h"
//#include "vcl.h"
//#include "hash_map.h"
//#include "exception.h"

#define DebugAssert(cond, str) assert(cond)

namespace Java_cvc3_JniUtils {

  /// Embedding of c++ objects in java objects

  // generic delete function for any type T
  template <class T> class DeleteEmbedded {
  public:
    static void deleteEmbedded(void* cobj) {
      delete (T*) cobj;
    }
  };

  typedef void (*TDeleteEmbedded)(void*);


  // Encapsulates a c++ object so that:
  // - (un)embedding casting is type safe
  // - deallocation is automatic (if needed)
  // This has probably quit a bit of overhead, because now for each
  // wrapper object (even if only a temporary reference) an instance
  // of Embedded is created.
  // But considering the above two benefits it should be worth it
  // because it should simplify maintenance quite a bit,
  // as changes in the cvc API should lead to assertion failures
  // instead of strange bugs.
  class Embedded {
  private:
    // the actual embedded c++ object,
    // as void* to make Embedded independent of its type
    void* d_cobj;

    // the type info of d_cobj,
    // to make sure that later unembeddings are type safe
    // actually only needed in debugging, so might be guarded with IF_DEBUG
    const std::type_info& d_typeInfo;

    // the type correct delete function for d_cobj,
    // or NULL if this embedding is merely a reference
    // and not responsible for its deallocation
    TDeleteEmbedded d_delete;

  public:
    Embedded(void* cobj, const std::type_info& ti, TDeleteEmbedded del) :
      d_cobj(cobj), d_typeInfo(ti), d_delete(del) {
	assert(d_cobj != NULL);
    }

    ~Embedded() {
      assert(d_cobj != NULL);
      if (d_delete != NULL) d_delete(d_cobj);
    }

    const void* getCObj() const {
      return d_cobj;
    }

    const std::type_info& getType() const {
      return d_typeInfo;
    }
  };



  // embed functions

  // embeds a c++ object of type T into a jobject
  // by first wrapping it into an Embedded object.
  template <class T> jobject embed(JNIEnv* env, T* cobj, const std::type_info& ti,
				   TDeleteEmbedded del) {
    DebugAssert(cobj != NULL, "JniUtils::embed: null object given");
    Embedded* embedded = new Embedded((void*)cobj, ti, del);
    return (jobject)env->NewDirectByteBuffer(embedded, sizeof(Embedded));
  }

  // embeds a constant reference to a c++ object into a jobject
  template <class T> jobject embed_const_ref(JNIEnv* env, const T* cobj) {
    DebugAssert(cobj != NULL, "JniUtils::embed_const: null object given");
    return embed<T>(env, (T*) cobj, typeid(cobj), NULL);
  }

  // embeds a mutable reference to a c++ object into a jobject
  template <class T> jobject embed_mut_ref(JNIEnv* env, T* cobj) {
    DebugAssert(cobj != NULL, "JniUtils::embed_mut_ref: null object given");
    return embed<T>(env, (T*) cobj, typeid(cobj), NULL);
  }

  // embeds a fresh copy of a (probably temporary) c++ object into a jobject
  template <class T> jobject embed_copy(JNIEnv* env, const T& cobj) {
    DebugAssert(&cobj != NULL, "JniUtils::embed_copy: null object given");
    T* copy = new T(cobj);
    assert(copy != NULL);
    return embed<T>(env, copy, typeid(copy), &DeleteEmbedded<T>::deleteEmbedded);
  }

  // embeds a c++ object into a jobject,
  // and takes over the responsibility to deallocate it
  template <class T> jobject embed_own(JNIEnv* env, T* cobj) {
    DebugAssert(cobj != NULL, "JniUtils::embed_own: null object given");
    return embed<T>(env, cobj, typeid(cobj), &DeleteEmbedded<T>::deleteEmbedded);
  }


  // unembed functions

  // extract Embedded* from a jobject
  Embedded* unembed(JNIEnv* env, jobject jobj);

  // extract a constant c++ object of type T from a jobject
  template <class T> const T* unembed_const(JNIEnv* env, jobject jobj) {
    Embedded* embedded = unembed(env, jobj);
    return (const T*) embedded->getCObj();
  }

  // extract a mutable c++ object of type T from a jobject
  template <class T> T* unembed_mut(JNIEnv* env, jobject jobj) {
    Embedded* embedded = unembed(env, jobj);
    // check that the wrapped object is not const
    DebugAssert(embedded->getType() == typeid(T*),
		"JniUtils::unembed_mut: type mismatch");
    return (T*) embedded->getCObj();
  }


  // delete embedded

  // delete the Embedded object contained in a jobject,
  // and also destruct the wrapped c++ object if necessary.
  void deleteEmbedded(JNIEnv* env, jobject jobj);




  /// Conversions between c++ and java

  // bool
  bool toCpp(jboolean j);

  // string
  jstring toJava(JNIEnv* env, const std::string& cstring);
  jstring toJava(JNIEnv* env, const char* cstring);
  std::string toCpp(JNIEnv* env, const jstring& string);

  // enums
  jstring toJava(JNIEnv* env, CVC3::QueryResult result);
  jstring toJava(JNIEnv* env, CVC3::FormulaValue result);
  jstring toJava(JNIEnv* env, CVC3::InputLanguage result);
  CVC3::InputLanguage toCppInputLanguage(JNIEnv* env, const std::string& lang);

  // exceptions
  void toJava(JNIEnv* env, const CVC3::Exception& e);

  // vectors
  template <class T> jobjectArray toJavaVCopy(JNIEnv* env, const std::vector<T>& v) {
    jobjectArray jarray = (jobjectArray)
      env->NewObjectArray(
	v.size(),
	env->FindClass("java/lang/Object"),
	NULL);

    for (size_t i = 0; i < v.size(); ++i) {
      env->SetObjectArrayElement(jarray, i, embed_copy<T>(env, v[i]));
    }

    return jarray;
  }

  template <class T> jobjectArray toJavaVConstRef(JNIEnv* env, const std::vector<T>& v) {
    jobjectArray jarray = (jobjectArray)
      env->NewObjectArray(
	v.size(),
	env->FindClass("java/lang/Object"),
	NULL);

    for (size_t i = 0; i < v.size(); ++i) {
      env->SetObjectArrayElement(jarray, i, embed_const_ref<T>(env, &v[i]));
    }

    return jarray;
  }

  template<class T>
    jobjectArray
    toJavaVVConstRef(JNIEnv* env, const std::vector<std::vector<T> >& v)
    {
      jobjectArray jarray = (jobjectArray) env->NewObjectArray(v.size(),
          env->FindClass("[Ljava/lang/Object;"), NULL);
      for (size_t i = 0; i < v.size(); ++i)
        {
          env->SetObjectArrayElement(jarray, i, toJavaVConstRef(env, v[i]));
        }
      return jarray;
    }

  template <class T> std::vector<T> toCppV(JNIEnv* env, const jobjectArray& jarray) {
    std::vector<T> v;
    int length = env->GetArrayLength(jarray);
    for (int i = 0; i < length; ++i) {
      v.push_back(*unembed_const<T>(env, env->GetObjectArrayElement(jarray, i)));
    }
    return v;
  }

  template <class T> std::vector<std::vector<T> > toCppVV(JNIEnv* env, const jobjectArray& jarray) {
    std::vector<std::vector<T> > v;
    int length = env->GetArrayLength(jarray);
    for (int i = 0; i < length; ++i) {
      jobjectArray jsub = static_cast<jobjectArray>(env->GetObjectArrayElement(jarray, i));
      v.push_back(toCppV<T>(env, jsub));
    }
    return v;
  }

  template <class T> std::vector<std::vector<std::vector<T> > >
    toCppVVV(JNIEnv* env, const jobjectArray& jarray) {
    std::vector<std::vector<std::vector<T> > > v;
    int length = env->GetArrayLength(jarray);
    for (int i = 0; i < length; ++i) {
      jobjectArray jsub = static_cast<jobjectArray>(env->GetObjectArrayElement(jarray, i));
      v.push_back(toCppVV<T>(env, jsub));
    }
    return v;
  }

  // string vectors
  std::vector<std::string> toCppV(JNIEnv* env, const jobjectArray& jarray);
  std::vector<std::vector<std::string> > toCppVV(JNIEnv* env, const jobjectArray& jarray);
  std::vector<std::vector<std::vector<std::string> > > toCppVVV(JNIEnv* env, const jobjectArray& jarray);
  jobjectArray toJavaV(JNIEnv* env, const std::vector<std::string>& v);

  // primitive vectors
  std::vector<bool> toCppV(JNIEnv* env, const jbooleanArray& jarray);


  // hash map
  /*template <class K, class V> jobjectArray toJavaHCopy(JNIEnv* env, const Hash::hash_map<K, V>& hm) {
    jobjectArray jarray = (jobjectArray)
      env->NewObjectArray(
	hm.size() * 2,
	env->FindClass("java/lang/Object"),
	NULL);

    int i = 0;
    typename Hash::hash_map<K, V>::const_iterator it;
    for (it = hm.begin(); it != hm.end(); ++it) {
      assert(i < env->GetArrayLength(jarray));
      env->SetObjectArrayElement(jarray, i, embed_copy<K>(env, it->first));
      ++i;
      assert(i < env->GetArrayLength(jarray));
      env->SetObjectArrayElement(jarray, i, embed_copy<V>(env, it->second));
      ++i;
    }
    return jarray;
  }*/

  template <class V> jobjectArray toJavaHCopy(JNIEnv* env, const CVC3::ExprMap<V>& hm) {
    jobjectArray jarray = (jobjectArray)
      env->NewObjectArray(
	hm.size() * 2,
	env->FindClass("java/lang/Object"),
	NULL);

    int i = 0;
    typename CVC3::ExprMap<V>::const_iterator it;
    for (it = hm.begin(); it != hm.end(); ++it) {
      assert(i < env->GetArrayLength(jarray));
      env->SetObjectArrayElement(jarray, i, embed_copy<CVC3::Expr>(env, it->first));
      ++i;
      assert(i < env->GetArrayLength(jarray));
      env->SetObjectArrayElement(jarray, i, embed_copy<V>(env, it->second));
      ++i;
    }
    return jarray;
  }

}


#endif
