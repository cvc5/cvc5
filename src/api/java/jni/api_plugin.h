
/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
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

#ifndef CVC5__API_PLUGIN_H
#define CVC5__API_PLUGIN_H
#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <jni.h>

#include <string>
#include <vector>

class ApiPlugin : public cvc5::Plugin
{
 public:
  ApiPlugin(cvc5::TermManager& tm, JNIEnv* env, jobject plugin);
  /**
   * Call to check, return vector of lemmas to add to the SAT solver.
   * This method is called periodically, roughly at every SAT decision.
   *
   * @return The vector of lemmas to add to the SAT solver.
   */
  std::vector<cvc5::Term> check() override;
  /**
   * Notify SAT clause, called when cl is a clause learned by the SAT solver.
   *
   * @param cl The learned clause.
   */
  void notifySatClause(const cvc5::Term& cl) override;
  /**
   * Notify theory lemma, called when lem is a theory lemma sent by a theory
   * solver.
   *
   * @param lem The theory lemma.
   */
  void notifyTheoryLemma(const cvc5::Term& lem) override;
  /**
   * Get the name of the plugin (for debugging).
   *
   * @return The name of the plugin.
   */
  std::string getName() override;

 private:
  /** call a void function that receives a term in class AbstractPlugin  */
  void notifyHelper(const char* functionName, const cvc5::Term& cl);

  /** Reference to java environment */
  JNIEnv* d_env;
  /** Reference to the term manager */
  cvc5::TermManager& d_tm;
  /** Reference to java plugin object */
  jobject d_plugin;
};

#endif  // CVC5__API_PLUGIN_H
