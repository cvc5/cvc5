/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Abdalrhman Mohamed, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5.api;

public class Grammar extends AbstractPointer
{
  // region construction and destruction
  Grammar(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  public Grammar(Grammar grammar)
  {
    super(grammar.solver, copyGrammar(grammar.pointer));
  }

  private static native long copyGrammar(long pointer);

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /**
   * Add \p rule to the set of rules corresponding to \p ntSymbol.
   * @param ntSymbol the non-terminal to which the rule is added
   * @param rule the rule to add
   */
  public void addRule(Term ntSymbol, Term rule)
  {
    addRule(pointer, ntSymbol.getPointer(), rule.getPointer());
  }

  private native void addRule(long pointer, long ntSymbolPointer, long rulePointer);

  /**
   * Add \p rules to the set of rules corresponding to \p ntSymbol.
   * @param ntSymbol the non-terminal to which the rules are added
   * @param rules the rules to add
   */
  public void addRules(Term ntSymbol, Term[] rules)
  {
    long[] pointers = Utils.getPointers(rules);
    addRules(pointer, ntSymbol.getPointer(), pointers);
  }

  public native void addRules(long pointer, long ntSymbolPointer, long[] rulePointers);

  /**
   * Allow \p ntSymbol to be an arbitrary constant.
   * @param ntSymbol the non-terminal allowed to be any constant
   */
  public void addAnyConstant(Term ntSymbol)
  {
    addAnyConstant(pointer, ntSymbol.getPointer());
  }

  private native void addAnyConstant(long pointer, long ntSymbolPointer);

  /**
   * Allow \p ntSymbol to be any input variable to corresponding
   * synth-fun/synth-inv with the same sort as \p ntSymbol.
   * @param ntSymbol the non-terminal allowed to be any input constant
   */
  public void addAnyVariable(Term ntSymbol)
  {
    addAnyVariable(pointer, ntSymbol.getPointer());
  }

  private native void addAnyVariable(long pointer, long ntSymbolPointer);

  /**
   * @return a string representation of this grammar.
   */
  protected native String toString(long pointer);
}
