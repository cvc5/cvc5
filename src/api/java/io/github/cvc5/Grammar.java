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

import java.lang.foreign.Arena;

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
  Grammar(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, Grammar::deletePointer);
  }

  /**
   * Constructs a new {@code Grammar} instance by creating a deep copy of
   * the specified {@code Grammar}.
   *
   * @param grammar The {@code Grammar} instance to copy.
   */
  public Grammar(Grammar grammar)
  {
    super(grammar.ctx, copyGrammar(grammar.getPointer()), Grammar::deletePointer);
  }

  private static long copyGrammar(long pointer)
  {
    return CApi.cvc5_grammar_copy(pointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_grammar_release(pointer);
  }

  // endregion

  /**
   * Determine if this is the null grammar.
   * @return True if this Grammar is the null grammar.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private boolean isNull(long pointer)
  {
    return pointer == 0;
  }

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
    return equals(getPointer(), grammar.getPointer());
  }

  private boolean equals(long pointer1, long pointer2)
  {
    return CApi.cvc5_grammar_is_equal(pointer1, pointer2);
  }

  /**
   * Add {@code rule} to the set of rules corresponding to {@code ntSymbol}.
   * @param ntSymbol the non-terminal to which the rule is added.
   * @param rule the rule to add.
   */
  public void addRule(Term ntSymbol, Term rule)
  {
    addRule(getPointer(), ntSymbol.getPointer(), rule.getPointer());
  }

  private void addRule(long pointer, long ntSymbolPointer, long rulePointer)
  {
    CApi.cvc5_grammar_add_rule(pointer, ntSymbolPointer, rulePointer);
  }

  /**
   * Add {@code rules} to the set of rules corresponding to {@code ntSymbol}.
   * @param ntSymbol the non-terminal to which the rules are added.
   * @param rules the rules to add.
   */
  public void addRules(Term ntSymbol, Term[] rules)
  {
    long[] pointers = Utils.getPointers(rules);
    addRules(getPointer(), ntSymbol.getPointer(), pointers);
  }

  private void addRules(long pointer, long ntSymbolPointer, long[] rulePointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_grammar_add_rules(
          pointer, ntSymbolPointer, rulePointers.length, Native.longs(arena, rulePointers));
    }
  }

  /**
   * Allow {@code ntSymbol} to be an arbitrary constant.
   * @param ntSymbol the non-terminal allowed to be any constant.
   */
  public void addAnyConstant(Term ntSymbol)
  {
    addAnyConstant(getPointer(), ntSymbol.getPointer());
  }

  private void addAnyConstant(long pointer, long ntSymbolPointer)
  {
    CApi.cvc5_grammar_add_any_constant(pointer, ntSymbolPointer);
  }

  /**
   * Allow {@code ntSymbol} to be any input variable to corresponding
   * {@code synth-fun} or {@code synth-inv} with the same sort as
   * {@code ntSymbol}.
   * @param ntSymbol the non-terminal allowed to be any input constant.
   */
  public void addAnyVariable(Term ntSymbol)
  {
    addAnyVariable(getPointer(), ntSymbol.getPointer());
  }

  private void addAnyVariable(long pointer, long ntSymbolPointer)
  {
    CApi.cvc5_grammar_add_any_variable(pointer, ntSymbolPointer);
  }

  /**
   * @return A String representation of this grammar.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      return "";
    }
    return Native.string(CApi.cvc5_grammar_to_string(pointer));
  }

  /**
   * Get the hash value of a grammar.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(getPointer()));
  }

  private long hashCode(long pointer)
  {
    if (pointer == 0)
    {
      return 0;
    }
    return CApi.cvc5_grammar_hash(pointer);
  }
}
