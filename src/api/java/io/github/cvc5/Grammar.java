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

import java.util.Map;

/**
 * A Sygus Grammar.
 *
 * This class can be used to define a context-free grammar of terms. Its
 * interface coincides with the definition of grammars ({@code GrammarDef}) in
 * the SyGuS IF 2.1 standard.
 */
public class Grammar extends AbstractPointer
{
  // region construction and destruction
  Grammar(long pointer)
  {
    super(pointer);
  }

  /**
   * Constructs a new {@code Grammar} instance by creating a deep copy of
   * the specified {@code Grammar}.
   *
   * @param grammar The {@code Grammar} instance to copy.
   */
  public Grammar(Grammar grammar)
  {
    super(copyGrammar(grammar.pointer));
  }

  private static native long copyGrammar(long pointer);

  protected native void deletePointer(long pointer);

  // endregion

  /**
   * Determine if this is the null grammar.
   * @return True if this Grammar is the null grammar.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Referential equality operator.
   *
   * @param g The grammar to compare to for equality.
   * @return True if the gramamrs point to the same internal grammar object.
   */
  @Override
  public boolean equals(Object g)
  {
    if (this == g)
    {
      return true;
    }
    if (g == null || getClass() != g.getClass())
    {
      return false;
    }
    Grammar grammar = (Grammar) g;
    if (pointer == grammar.pointer)
    {
      return true;
    }
    return equals(pointer, grammar.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Add {@code rule} to the set of rules corresponding to {@code ntSymbol}.
   * @param ntSymbol the non-terminal to which the rule is added.
   * @param rule the rule to add.
   */
  public void addRule(Term ntSymbol, Term rule)
  {
    addRule(pointer, ntSymbol.getPointer(), rule.getPointer());
  }

  private native void addRule(long pointer, long ntSymbolPointer, long rulePointer);

  /**
   * Add {@code rule} to the set of rules corresponding to {@code ntSymbol},
   * with the specified weights.
   * @param ntSymbol the non-terminal to which the rule is added.
   * @param rule the rule to add.
   * @param weights the weights of this rule.
   */
  public void addRule(Term ntSymbol, Term rule, Map<Weight, Term> weights)
  {
    long[] weightPointers = new long[weights.size()];
    long[] termPointers = new long[weights.size()];
    int i = 0;
    for (Map.Entry<Weight, Term> entry : weights.entrySet())
    {
      weightPointers[i] = entry.getKey().getPointer();
      termPointers[i] = entry.getValue().getPointer();
      i++;
    }
    addRule(pointer, ntSymbol.getPointer(), rule.getPointer(), weightPointers, termPointers);
  }

  private native void addRule(long pointer,
      long ntSymbolPointer,
      long rulePointer,
      long[] weightPointers,
      long[] termPointers);

  /**
   * Add {@code rules} to the set of rules corresponding to {@code ntSymbol}.
   * @param ntSymbol the non-terminal to which the rules are added.
   * @param rules the rules to add.
   */
  public void addRules(Term ntSymbol, Term[] rules)
  {
    long[] pointers = Utils.getPointers(rules);
    addRules(pointer, ntSymbol.getPointer(), pointers);
  }

  private native void addRules(long pointer, long ntSymbolPointer, long[] rulePointers);

  /**
   * Add {@code rules} to the set of rules corresponding to {@code ntSymbol},
   * each with a corresponding weight map.
   * @param ntSymbol the non-terminal to which the rules are added.
   * @param rules the rules to add.
   * @param weights the weights for each rule.
   */
  public void addRules(Term ntSymbol, Term[] rules, Map<Weight, Term>[] weights)
  {
    long[] rulePointers = Utils.getPointers(rules);
    long[][] weightPointers = new long[weights.length][];
    long[][] termPointers = new long[weights.length][];
    for (int i = 0; i < weights.length; i++)
    {
      Map<Weight, Term> map = weights[i];
      weightPointers[i] = new long[map.size()];
      termPointers[i] = new long[map.size()];
      int j = 0;
      for (Map.Entry<Weight, Term> entry : map.entrySet())
      {
        weightPointers[i][j] = entry.getKey().getPointer();
        termPointers[i][j] = entry.getValue().getPointer();
        j++;
      }
    }
    addRules(pointer, ntSymbol.getPointer(), rulePointers, weightPointers, termPointers);
  }

  private native void addRules(long pointer,
      long ntSymbolPointer,
      long[] rulePointers,
      long[][] weightPointers,
      long[][] termPointers);

  /**
   * Allow {@code ntSymbol} to be an arbitrary constant.
   * @param ntSymbol the non-terminal allowed to be any constant.
   */
  public void addAnyConstant(Term ntSymbol)
  {
    addAnyConstant(pointer, ntSymbol.getPointer());
  }

  private native void addAnyConstant(long pointer, long ntSymbolPointer);

  /**
   * Allow {@code ntSymbol} to be an arbitrary constant, with specified weights.
   * @param ntSymbol the non-terminal allowed to be any constant.
   * @param weights the weights of this rule.
   */
  public void addAnyConstant(Term ntSymbol, Map<Weight, Term> weights)
  {
    long[] weightPointers = new long[weights.size()];
    long[] termPointers = new long[weights.size()];
    int i = 0;
    for (Map.Entry<Weight, Term> entry : weights.entrySet())
    {
      weightPointers[i] = entry.getKey().getPointer();
      termPointers[i] = entry.getValue().getPointer();
      i++;
    }
    addAnyConstant(pointer, ntSymbol.getPointer(), weightPointers, termPointers);
  }

  private native void addAnyConstant(
      long pointer, long ntSymbolPointer, long[] weightPointers, long[] termPointers);

  /**
   * Allow {@code ntSymbol} to be any input variable to corresponding
   * {@code synth-fun} or {@code synth-inv} with the same sort as
   * {@code ntSymbol}.
   * @param ntSymbol the non-terminal allowed to be any input constant.
   */
  public void addAnyVariable(Term ntSymbol)
  {
    addAnyVariable(pointer, ntSymbol.getPointer());
  }

  private native void addAnyVariable(long pointer, long ntSymbolPointer);

  /**
   * Allow {@code ntSymbol} to be any input variable, with specified weights.
   * @param ntSymbol the non-terminal allowed to be any input variable.
   * @param weights the weights of this rule.
   */
  public void addAnyVariable(Term ntSymbol, Map<Weight, Term> weights)
  {
    long[] weightPointers = new long[weights.size()];
    long[] termPointers = new long[weights.size()];
    int i = 0;
    for (Map.Entry<Weight, Term> entry : weights.entrySet())
    {
      weightPointers[i] = entry.getKey().getPointer();
      termPointers[i] = entry.getValue().getPointer();
      i++;
    }
    addAnyVariable(pointer, ntSymbol.getPointer(), weightPointers, termPointers);
  }

  private native void addAnyVariable(
      long pointer, long ntSymbolPointer, long[] weightPointers, long[] termPointers);

  /**
   * @return A String representation of this grammar.
   */
  protected native String toString(long pointer);

  /**
   * Get the hash value of a grammar.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return hashCode(pointer);
  }

  private native int hashCode(long pointer);
}
