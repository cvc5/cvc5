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

import io.github.cvc5.capi.CApi;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;

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
  Grammar(NativeContext ctx, MemorySegment pointer)
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
    super(grammar.ctx, copyGrammar(grammar.handle()), Grammar::deletePointer);
  }

  private static MemorySegment copyGrammar(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_grammar_copy(pointer));
  }

  private static void deletePointer(MemorySegment pointer)
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
    return isNull(handle());
  }

  private boolean isNull(MemorySegment pointer)
  {
    return pointer.address() == 0;
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
    if (address() == grammar.address())
    {
      return true;
    }
    return equals(handle(), grammar.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_grammar_is_equal(pointer1, pointer2));
  }

  /**
   * Add {@code rule} to the set of rules corresponding to {@code ntSymbol}.
   * @param ntSymbol the non-terminal to which the rule is added.
   * @param rule the rule to add.
   */
  public void addRule(Term ntSymbol, Term rule)
  {
    addRule(handle(), ntSymbol.handle(), rule.handle());
  }

  private void addRule(
      MemorySegment pointer, MemorySegment ntSymbolPointer, MemorySegment rulePointer)
  {
    CApi.cvc5_grammar_add_rule(pointer, ntSymbolPointer, rulePointer);
    Native.check();
  }

  /**
   * Add {@code rules} to the set of rules corresponding to {@code ntSymbol}.
   * @param ntSymbol the non-terminal to which the rules are added.
   * @param rules the rules to add.
   */
  public void addRules(Term ntSymbol, Term[] rules)
  {
    MemorySegment[] pointers = Utils.getHandles(rules);
    addRules(handle(), ntSymbol.handle(), pointers);
  }

  private void addRules(
      MemorySegment pointer, MemorySegment ntSymbolPointer, MemorySegment[] rulePointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      CApi.cvc5_grammar_add_rules(pointer,
          ntSymbolPointer,
          rulePointers.length,
          Native.allocateHandles(arena, rulePointers));
      Native.check();
    }
  }

  /**
   * Allow {@code ntSymbol} to be an arbitrary constant.
   * @param ntSymbol the non-terminal allowed to be any constant.
   */
  public void addAnyConstant(Term ntSymbol)
  {
    addAnyConstant(handle(), ntSymbol.handle());
  }

  private void addAnyConstant(MemorySegment pointer, MemorySegment ntSymbolPointer)
  {
    CApi.cvc5_grammar_add_any_constant(pointer, ntSymbolPointer);
    Native.check();
  }

  /**
   * Allow {@code ntSymbol} to be any input variable to corresponding
   * {@code synth-fun} or {@code synth-inv} with the same sort as
   * {@code ntSymbol}.
   * @param ntSymbol the non-terminal allowed to be any input constant.
   */
  public void addAnyVariable(Term ntSymbol)
  {
    addAnyVariable(handle(), ntSymbol.handle());
  }

  private void addAnyVariable(MemorySegment pointer, MemorySegment ntSymbolPointer)
  {
    CApi.cvc5_grammar_add_any_variable(pointer, ntSymbolPointer);
    Native.check();
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
    return Native.string(CApi.cvc5_grammar_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * Get the hash value of a grammar.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(handle()));
  }

  private long hashCode(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      return 0;
    }
    return Native.check(CApi.cvc5_grammar_hash(pointer));
  }
}
