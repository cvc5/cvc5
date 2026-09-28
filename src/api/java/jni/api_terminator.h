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

#ifndef CVC5__API_TERMINATOR_H
#define CVC5__API_TERMINATOR_H

#include <cvc5/cvc5.h>
#include <jni.h>

/**
 * Terminator that calls method terminate() of a Java object, which is the
 * wrapper of the terminator connected to a Java solver.
 */
class ApiTerminator : public cvc5::Terminator
{
 public:
  /**
   * Constructor.
   * @param env The JNI environment.
   * @param terminator The Java object.
   */
  ApiTerminator(JNIEnv* env, jobject terminator);
  /**
   * Release the global reference to the Java object. Must be called before
   * this terminator is destroyed.
   * @param env The JNI environment.
   */
  void release(JNIEnv* env);
  bool terminate() override;

 private:
  /** The Java VM, to get the JNI environment of the thread of the query. */
  JavaVM* d_vm;
  /** Global reference to the Java object. */
  jobject d_terminator;
  /** Method terminate() of the Java object. */
  jmethodID d_terminate;
};

#endif  // CVC5__API_TERMINATOR_H
