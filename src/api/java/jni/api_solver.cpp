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

#include "api_solver.h"

#include <cvc5/cvc5.h>

#include "api_plugin.h"

using namespace cvc5;

ApiSolver::ApiSolver(TermManager& tm) : Solver(tm) {}

jobject ApiSolver::addGlobalReference(JNIEnv* env, jobject object)
{
  jobject reference = env->NewGlobalRef(object);
  d_globalReferences.push_back(reference);
  return reference;
}

void ApiSolver::addPluginPointer(jlong pluginPointer)
{
  d_pluginPointers.push_back(pluginPointer);
}

void ApiSolver::connectTerminator(JNIEnv* env, jobject terminator)
{
  std::unique_ptr<ApiTerminator> t;
  if (terminator != nullptr)
  {
    t.reset(new ApiTerminator(env, terminator));
  }
  setTerminator(t.get());
  // release the previously connected terminator after disconnecting it
  if (d_terminator)
  {
    d_terminator->release(env);
  }
  d_terminator = std::move(t);
}

void ApiSolver::deletePointers(JNIEnv* env)
{
  connectTerminator(env, nullptr);
  for (jobject ref : d_globalReferences)
  {
    env->DeleteGlobalRef(ref);
  }
  for (jlong p : d_pluginPointers)
  {
    ApiPlugin* plugin = reinterpret_cast<ApiPlugin*>(p);
    delete plugin;
  }
  d_globalReferences.clear();
  d_pluginPointers.clear();
}
