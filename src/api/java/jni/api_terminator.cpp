/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */
#include "api_terminator.h"

#include "api_utilities.h"

ApiTerminator::ApiTerminator(JNIEnv* env, jobject terminator)
    : d_vm(nullptr), d_terminator(env->NewWeakGlobalRef(terminator))
{
  env->GetJavaVM(&d_vm);
  jclass terminatorClass = env->GetObjectClass(terminator);
  d_terminate = env->GetMethodID(terminatorClass, "terminate", "()Z");
}

void ApiTerminator::release(JNIEnv* env)
{
  env->DeleteWeakGlobalRef(d_terminator);
  d_terminator = nullptr;
}

bool ApiTerminator::terminate() noexcept
{
  JNIEnv* env = getEnv(d_vm);
  jobject terminator = env->NewLocalRef(d_terminator);
  if (terminator == nullptr)
  {
    return false;
  }
  // Exceptions of the terminator are remembered by the Java object.
  jboolean res = env->CallBooleanMethod(terminator, d_terminate);
  env->DeleteLocalRef(terminator);
  if (env->ExceptionCheck())
  {
    // Not expected, but exceptions must not be pending during the query.
    env->ExceptionDescribe();
    env->ExceptionClear();
    return true;
  }
  return res == JNI_TRUE;
}
