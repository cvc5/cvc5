/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
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

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_InputParser_deletePointer(
    JNIEnv* env, jobject, jlong pointer)
{
  delete reinterpret_cast<InputParser*>(pointer);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    getSolver
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_InputParser_getSolver(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  Solver* solver = parser->getSolver();
  return reinterpret_cast<jlong>(solver);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    getSymbolManager
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_InputParser_getSymbolManager(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  SymbolManager* symbolManager = parser->getSymbolManager();
  return reinterpret_cast<jlong>(symbolManager);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    setFileInput
 * Signature: (JILjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_InputParser_setFileInput(
    JNIEnv* env, jobject, jlong pointer, jint langValue, jstring jFileName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(langValue);
  const char* cFileName = env->GetStringUTFChars(jFileName, nullptr);
  std::string sFileName(cFileName);
  parser->setFileInput(lang, sFileName);
  env->ReleaseStringUTFChars(jFileName, cFileName);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    setStringInput
 * Signature: (JILjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_InputParser_setStringInput(JNIEnv* env,
                                               jobject,
                                               jlong pointer,
                                               jint langValue,
                                               jstring jInput,
                                               jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(langValue);
  const char* cInput = env->GetStringUTFChars(jInput, nullptr);
  std::string sInput(cInput);
  const char* cName = env->GetStringUTFChars(jName, nullptr);
  std::string sName(cName);
  parser->setStringInput(lang, sInput, sName);
  env->ReleaseStringUTFChars(jName, cName);
  env->ReleaseStringUTFChars(jName, cInput);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    setIncrementalStringInput
 * Signature: (JILjava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_InputParser_setIncrementalStringInput(
    JNIEnv* env, jobject, jlong pointer, jint langValue, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  modes::InputLanguage lang = static_cast<modes::InputLanguage>(langValue);
  const char* cName = env->GetStringUTFChars(jName, nullptr);
  std::string sName(cName);
  parser->setIncrementalStringInput(lang, sName);
  env->ReleaseStringUTFChars(jName, cName);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    appendIncrementalStringInput
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_InputParser_appendIncrementalStringInput(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jstring jInput)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  const char* cInput = env->GetStringUTFChars(jInput, nullptr);
  std::string sInput(cInput);
  parser->appendIncrementalStringInput(sInput);
  env->ReleaseStringUTFChars(jInput, cInput);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    nextCommand
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_InputParser_nextCommand(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  Command* command = new Command(parser->nextCommand());
  return reinterpret_cast<jlong>(command);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    nextTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_InputParser_nextTerm(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  Term* term = new Term(parser->nextTerm());
  return reinterpret_cast<jlong>(term);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_InputParser
 * Method:    done
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_InputParser_done(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  InputParser* parser = reinterpret_cast<InputParser*>(pointer);
  return static_cast<jboolean>(parser->done());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}
