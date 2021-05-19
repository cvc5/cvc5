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

#include "cvc5_Solver.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Solver
 * Method:    newSolver
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_newSolver(JNIEnv*, jobject)
{
  Solver* solver = new Solver();
  return ((jlong)solver);
}

/*
 * Class:     cvc5_Solver
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_deletePointer(JNIEnv*,
                                                     jclass,
                                                     jlong pointer)
{
  delete ((Solver*)pointer);
}

/*
 * Class:     cvc5_Solver
 * Method:    setLogic
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_setLogic(JNIEnv* env,
                                                jobject,
                                                jlong solverPointer,
                                                jstring jLogic)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)solverPointer;
  const char* cLogic = env->GetStringUTFChars(jLogic, nullptr);
  solver->setLogic(std::string(cLogic));

  CVC5_JAVA_API_TRY_CATCH_END(env);
}
