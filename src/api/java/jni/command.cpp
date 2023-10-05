/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

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
