#ifndef CVC__JAVA_API_H
#define CVC__JAVA_API_H

#include <iostream>

#define CVC_JAVA_API_TRY_CATCH_BEGIN \
  try                                \
  {
#define CVC_JAVA_API_TRY_CATCH_END(env)                                       \
  }                                                                           \
  catch (const CVC4ApiRecoverableException& e)                                \
  {                                                                           \
    jclass exceptionClass = env->FindClass("cvc/CVCApiRecoverableException"); \
    env->ThrowNew(exceptionClass, e.what());                                  \
  }                                                                           \
  catch (const CVC4ApiException& e)                                           \
  {                                                                           \
    jclass exceptionClass = env->FindClass("cvc/CVCApiException");            \
    env->ThrowNew(exceptionClass, e.what());                                  \
  }
#define CVC_JAVA_API_TRY_CATCH_END_RETURN(env, returnValue) \
  CVC_JAVA_API_TRY_CATCH_END(env)                           \
  return returnValue;
#endif  // CVC__JAVA_API_H
