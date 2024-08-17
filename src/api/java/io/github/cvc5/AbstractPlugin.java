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
 * The cvc5 java API.
 */

package io.github.cvc5;

public abstract class AbstractPlugin
{
  /**
   * Create plugin instance.
   * @param tm The associated term manager.
   */
  public AbstractPlugin(TermManager tm)
  {
    this.termManager = tm;
  }

  protected final TermManager termManager;

  /**
   * Get the associated term manager instance
   * @return The term manager.
   */
  public TermManager getTermManager()
  {
    return termManager;
  }

  /**
   * Call to check, return vector of lemmas to add to the SAT solver.
   * This method is called periodically, roughly at every SAT decision.
   *
   * @return The vector of lemmas to add to the SAT solver.
   */
  public Term[] check()
  {
    return new Term[0];
  }

  /**
   * Notify SAT clause, called when cl is a clause learned by the SAT solver.
   *
   * @param cl The learned clause.
   */
  public void notifySatClause(Term cl) {}

  /**
   * Notify theory lemma, called when lem is a theory lemma sent by a theory
   * solver.
   *
   * @param lem The theory lemma.
   */
  public void notifyTheoryLemma(Term lem) {}

  /**
   * Get the name of the plugin (for debugging).
   *
   * @return The name of the plugin.
   */
  public abstract String getName();
}
