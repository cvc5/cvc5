/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#ifndef CVC5__JAVA_API_H
#define CVC5__JAVA_API_H

#define CVC5_JAVA_API_TRY_CATCH_BEGIN \
  try                                 \
  {
#define CVC5_JAVA_API_TRY_CATCH_END(env)                             \
  }                                                                  \
  catch (const CVC5ApiRecoverableException& e)                       \
  {                                                                  \
    jclass exceptionClass =                                          \
        env->FindClass("cvc5/CVC5ApiRecoverableException");          \
    env->ThrowNew(exceptionClass, e.what());                         \
  }                                                                  \
  catch (const CVC5ApiException& e)                                  \
  {                                                                  \
    jclass exceptionClass = env->FindClass("cvc5/CVC5ApiException"); \
    env->ThrowNew(exceptionClass, e.what());                         \
  }
#define CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, returnValue) \
  CVC5_JAVA_API_TRY_CATCH_END(env)                           \
  return returnValue;
#endif  // CVC5__JAVA_API_H
