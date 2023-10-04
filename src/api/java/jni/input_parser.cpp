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
#include "io_github_cvc5_InputParser.h"

using namespace cvc5;
using namespace cvc5::parser;

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    newInputParser
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_InputParser_newInputParser__JJ(
    JNIEnv* env, jclass, jlong solverPointer, jlong symbolManagerPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(solverPointer);
  SymbolManager* symbolManager =
      reinterpret_cast<SymbolManager*>(symbolManagerPointer);
  InputParser* parser = new InputParser(solver, symbolManager);
  return reinterpret_cast<jlong>(parser);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    newInputParser
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_InputParser_newInputParser__J(
    JNIEnv* env, jclass, jlong solverPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(solverPointer);
  InputParser* parser = new InputParser(solver);
  return reinterpret_cast<jlong>(parser);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}