/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#ifndef CVC5__API_SOLVER_H
#define CVC5__API_SOLVER_H
#include <cvc5/cvc5.h>
#include <jni.h>

class ApiSolver : public cvc5::Solver
{
 public:
  /**
   * Construct an ApiSolver.
   */
  ApiSolver(cvc5::TermManager& tm);

  /**
   * Create a new global reference to the object referred to by the obj
   * argument, and store the object to be disposed of later.
   *
   * Intended for objects requiring global lifetime management across JNI calls.
   * Currently used for oracles and plugins.
   */
  jobject addGlobalReference(JNIEnv* env, jobject object);
  /**
   * Store a plugin pointer to be deleted later.
   */
  void addPluginPointer(jlong pluginPointer);
  /**
   * Delete pointers and global references.
   */
  void deletePointers(JNIEnv* env);

 private:
  /**
   * A vector of jni global references that need to be freed when
   * the deletePointers method is called.
   */
  std::vector<jobject> d_globalReferences;
  /**
   * A vector of ApiPlugin pointers that need to be freed when
   * the deletePointers method is called.
   */
  std::vector<jlong> d_pluginPointers;
};

#endif  // CVC5__API_SOLVER_H