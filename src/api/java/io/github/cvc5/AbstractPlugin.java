/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

/**
 * A cvc5 plugin abstract class.
 */
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

  /** The associated term manager. */
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

  /*
   * Bridges called from native code. They exchange raw native pointers so
   * that Term wrappers are created here, in the context of the plugin's term
   * manager.
   */

  /**
   * Called from native code, see {@link #check()}.
   *
   * @return The native pointers of the lemmas, which native code copies
   *         before any further Java code can run on this thread.
   */
  final long[] checkNative()
  {
    Term[] lemmas = check();
    return lemmas == null ? new long[0] : Utils.getPointers(lemmas);
  }

  /**
   * Called from native code, see {@link #notifySatClause(Term)}.
   *
   * @param pointer The native pointer of the clause; ownership is transferred
   *                to the created wrapper.
   */
  final void notifySatClauseNative(long pointer)
  {
    notifySatClause(new Term(termManager.ctx, pointer));
  }

  /**
   * Called from native code, see {@link #notifyTheoryLemma(Term)}.
   *
   * @param pointer The native pointer of the lemma; ownership is transferred
   *                to the created wrapper.
   */
  final void notifyTheoryLemmaNative(long pointer)
  {
    notifyTheoryLemma(new Term(termManager.ctx, pointer));
  }
}
