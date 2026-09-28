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

ApiTerminator::ApiTerminator(JNIEnv* env, jobject terminator)
    : d_vm(nullptr), d_terminator(env->NewGlobalRef(terminator))
{
  env->GetJavaVM(&d_vm);
  jclass terminatorClass = env->GetObjectClass(terminator);
  d_terminate = env->GetMethodID(terminatorClass, "terminate", "()Z");
}

void ApiTerminator::release(JNIEnv* env)
{
  env->DeleteGlobalRef(d_terminator);
  d_terminator = nullptr;
}

bool ApiTerminator::terminate()
{
  JNIEnv* env = nullptr;
  if (d_vm->GetEnv(reinterpret_cast<void**>(&env), JNI_VERSION_1_6) != JNI_OK)
  {
    return false;
  }
  // Exceptions of the terminator are remembered by the Java object.
  jboolean res = env->CallBooleanMethod(d_terminator, d_terminate);
  if (env->ExceptionCheck())
  {
    // Not expected, but exceptions must not be pending during the query.
    env->ExceptionDescribe();
    env->ExceptionClear();
    return true;
  }
  return res == JNI_TRUE;
}
