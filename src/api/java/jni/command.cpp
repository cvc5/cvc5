/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <sstream>

#include "api_utilities.h"
#include "io_github_cvc5_Command.h"

using namespace cvc5;
using namespace cvc5::parser;

/*
 * Class:     io_github_cvc5_Command
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Command_deletePointer(JNIEnv*,
                                                                 jobject,
                                                                 jlong pointer)
{
  delete reinterpret_cast<Command*>(pointer);
}

/*
 * Class:     io_github_cvc5_Command
 * Method:    invoke
 * Signature: (JJJ)V
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_Command_invoke(JNIEnv* env,
                                   jobject,
                                   jlong pointer,
                                   jlong solverPointer,
                                   jlong symbolManagerPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Command* current = reinterpret_cast<Command*>(pointer);
  Solver* solver = reinterpret_cast<Solver*>(solverPointer);
  SymbolManager* symbolManager =
      reinterpret_cast<SymbolManager*>(symbolManagerPointer);
  std::stringstream ss;
  current->invoke(solver, symbolManager, ss);
  return env->NewStringUTF(ss.str().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Command
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Command_toString(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Command* current = reinterpret_cast<Command*>(pointer);
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Command
 * Method:    getCommandName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_Command_getCommandName(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Command* command = reinterpret_cast<Command*>(pointer);
  return env->NewStringUTF(command->getCommandName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Command
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Command_isNull(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Command* command = reinterpret_cast<Command*>(pointer);
  return static_cast<jboolean>(command->isNull());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}