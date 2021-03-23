//#include "cvc_Configuration.h"
//
//#include "cvc4/base/configuration.h"
//
//using namespace CVC4;
//
///*
// * Class:     cvc_Configuration
// * Method:    getName
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getName(JNIEnv* env, jclass)
//{
//  const char* cString = Configuration::getName().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isDebugBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isDebugBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isDebugBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isStatisticsBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isStatisticsBuild(JNIEnv*,
//                                                                    jclass)
//{
//  return (jboolean)Configuration::isStatisticsBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isTracingBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isTracingBuild(JNIEnv*,
//                                                                 jclass)
//{
//  return (jboolean)Configuration::isTracingBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isDumpingBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isDumpingBuild(JNIEnv*,
//                                                                 jclass)
//{
//  return (jboolean)Configuration::isDumpingBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isMuzzledBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isMuzzledBuild(JNIEnv*,
//                                                                 jclass)
//{
//  return (jboolean)Configuration::isMuzzledBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isAssertionBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isAssertionBuild(JNIEnv*,
//                                                                   jclass)
//{
//  return (jboolean)Configuration::isAssertionBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isProofBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isProofBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isProofBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isCoverageBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isCoverageBuild(JNIEnv*,
//                                                                  jclass)
//{
//  return (jboolean)Configuration::isCoverageBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isProfilingBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isProfilingBuild(JNIEnv*,
//                                                                   jclass)
//{
//  return (jboolean)Configuration::isProofBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isAsanBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isAsanBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isAsanBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isUbsanBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isUbsanBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isUbsanBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isTsanBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isTsanBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isTsanBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isCompetitionBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isCompetitionBuild(JNIEnv*,
//                                                                     jclass)
//{
//  return (jboolean)Configuration::isCompetitionBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isStaticBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isStaticBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isStaticBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getPackageName
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getPackageName(JNIEnv* env,
//                                                                jclass)
//{
//  const char* cString = Configuration::getPackageName().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getVersionString
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getVersionString(JNIEnv* env,
//                                                                  jclass)
//{
//  const char* cString = Configuration::getVersionString().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getVersionMajor
// * Signature: ()I
// */
//JNIEXPORT jint JNICALL Java_cvc_Configuration_getVersionMajor(JNIEnv*, jclass)
//{
//  return (jint)Configuration::getVersionMajor();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getVersionMinor
// * Signature: ()I
// */
//JNIEXPORT jint JNICALL Java_cvc_Configuration_getVersionMinor(JNIEnv*, jclass)
//{
//  return (jint)Configuration::getVersionMinor();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getVersionRelease
// * Signature: ()I
// */
//JNIEXPORT jint JNICALL Java_cvc_Configuration_getVersionRelease(JNIEnv*, jclass)
//{
//  return (jint)Configuration::getVersionRelease();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getVersionExtra
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getVersionExtra(JNIEnv* env,
//                                                                 jclass)
//{
//  const char* cString = Configuration::getVersionExtra().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    copyright
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_copyright(JNIEnv* env, jclass)
//{
//  const char* cString = Configuration::copyright().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    about
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_about(JNIEnv* env, jclass)
//{
//  const char* cString = Configuration::about().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    licenseIsGpl
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_licenseIsGpl(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::licenseIsGpl();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithGmp
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithGmp(JNIEnv*,
//                                                                 jclass)
//{
//  return (jboolean)Configuration::isBuiltWithGmp();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithCln
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithCln(JNIEnv*,
//                                                                 jclass)
//{
//  return (jboolean)Configuration::isBuiltWithCln();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithGlpk
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithGlpk(JNIEnv*,
//                                                                  jclass)
//{
//  return (jboolean)Configuration::isBuiltWithGlpk();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithAbc
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithAbc(JNIEnv*,
//                                                                 jclass)
//{
//  return (jboolean)Configuration::isBuiltWithAbc();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithCadical
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithCadical(JNIEnv*,
//                                                                     jclass)
//{
//  return (jboolean)Configuration::isBuiltWithCadical();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithCryptominisat
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL
//Java_cvc_Configuration_isBuiltWithCryptominisat(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isBuiltWithCryptominisat();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithKissat
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithKissat(JNIEnv*,
//                                                                    jclass)
//{
//  return (jboolean)Configuration::isBuiltWithKissat();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithDrat2Er
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithDrat2Er(JNIEnv*,
//                                                                     jclass)
//{
//  return (jboolean)Configuration::isBuiltWithDrat2Er();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithEditline
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithEditline(JNIEnv*,
//                                                                      jclass)
//{
//  return (jboolean)Configuration::isBuiltWithEditline();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithLfsc
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithLfsc(JNIEnv*,
//                                                                  jclass)
//{
//  return (jboolean)Configuration::isBuiltWithLfsc();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithPoly
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithPoly(JNIEnv*,
//                                                                  jclass)
//{
//  return (jboolean)Configuration::isBuiltWithPoly();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isBuiltWithSymFPU
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isBuiltWithSymFPU(JNIEnv*,
//                                                                    jclass)
//{
//  return (jboolean)Configuration::isBuiltWithSymFPU();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getNumDebugTags
// * Signature: ()I
// */
//JNIEXPORT jint JNICALL Java_cvc_Configuration_getNumDebugTags(JNIEnv*, jclass)
//{
//  return (jint)Configuration::getNumDebugTags();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getDebugTags
// * Signature: ()[Ljava/lang/String;
// */
//JNIEXPORT jobjectArray JNICALL Java_cvc_Configuration_getDebugTags(JNIEnv* env,
//                                                                   jclass)
//{
//  // get the number of tags
//  unsigned size = Configuration::getNumDebugTags();
//  // get the class of an array of strings
//  jclass stringArrayClass = env->FindClass("Ljava/lang/String;");
//  // allocate memory for the java array
//  jobjectArray jTags = env->NewObjectArray(size, stringArrayClass, nullptr);
//  // get the c++ array of tags
//  char const* const* cTags = Configuration::getDebugTags();
//  // fill the java array with tags
//  for (size_t i = 0; i < size; i++)
//  {
//    // get the c++ tag at index i
//    const char* cTag = cTags[i];
//    // convert the c++ tag into java tag
//    jstring jTag = env->NewStringUTF(cTag);
//    // set the java tag at index i
//    env->SetObjectArrayElement(jTags, i, (jobject)jTag);
//  }
//  // return the object array for java tags
//  return jTags;
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isDebugTag
// * Signature: (Ljava/lang/String;)Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isDebugTag(JNIEnv* env,
//                                                             jclass,
//                                                             jstring jString)
//{
//  const char* cString = env->GetStringUTFChars(jString, nullptr);
//  return (jboolean)Configuration::isDebugTag(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getNumTraceTags
// * Signature: ()I
// */
//JNIEXPORT jint JNICALL Java_cvc_Configuration_getNumTraceTags(JNIEnv*, jclass)
//{
//  return (jint)Configuration::getNumTraceTags();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getTraceTags
// * Signature: ()[Ljava/lang/String;
// */
//JNIEXPORT jobjectArray JNICALL Java_cvc_Configuration_getTraceTags(JNIEnv* env,
//                                                                   jclass)
//{
//  // get the number of tags
//  unsigned size = Configuration::getNumTraceTags();
//  // get the class of an array of strings
//  jclass stringArrayClass = env->FindClass("Ljava/lang/String;");
//  // allocate memory for the java array
//  jobjectArray jTags = env->NewObjectArray(size, stringArrayClass, nullptr);
//  // get the c++ array of tags
//  char const* const* cTags = Configuration::getTraceTags();
//  // fill the java array with tags
//  for (size_t i = 0; i < size; i++)
//  {
//    // get the c++ tag at index i
//    const char* cTag = cTags[i];
//    // convert the c++ tag into java tag
//    jstring jTag = env->NewStringUTF(cTag);
//    // set the java tag at index i
//    env->SetObjectArrayElement(jTags, i, (jobject)jTag);
//  }
//  // return the object array for java tags
//  return jTags;
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isTraceTag
// * Signature: (Ljava/lang/String;)Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isTraceTag(JNIEnv* env,
//                                                             jclass,
//                                                             jstring jString)
//{
//  const char* cString = env->GetStringUTFChars(jString, nullptr);
//  return (jboolean)Configuration::isTraceTag(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    isGitBuild
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_isGitBuild(JNIEnv*, jclass)
//{
//  return (jboolean)Configuration::isGitBuild();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getGitBranchName
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getGitBranchName(JNIEnv* env,
//                                                                  jclass)
//{
//  const char* cString = Configuration::getGitBranchName();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getGitCommit
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getGitCommit(JNIEnv* env,
//                                                              jclass)
//{
//  const char* cString = Configuration::getGitCommit();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    hasGitModifications
// * Signature: ()Z
// */
//JNIEXPORT jboolean JNICALL Java_cvc_Configuration_hasGitModifications(JNIEnv*,
//                                                                      jclass)
//{
//  return (jboolean)Configuration::hasGitModifications();
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getGitId
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getGitId(JNIEnv* env, jclass)
//{
//  const char* cString = Configuration::getGitId().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getCompiler
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL Java_cvc_Configuration_getCompiler(JNIEnv* env,
//                                                             jclass)
//{
//  const char* cString = Configuration::getCompiler().data();
//  return env->NewStringUTF(cString);
//}
//
///*
// * Class:     cvc_Configuration
// * Method:    getCompiledDateTime
// * Signature: ()Ljava/lang/String;
// */
//JNIEXPORT jstring JNICALL
//Java_cvc_Configuration_getCompiledDateTime(JNIEnv* env, jclass)
//{
//  const char* cString = Configuration::getCompiledDateTime().data();
//  return env->NewStringUTF(cString);
//}
