package cvc5;

public class Grammar extends AbstractPointer
{
  // region construction and destruction
  Grammar(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

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
    public void addRules(Term ntSymbol, Term [] rules)
    {
      long [] pointers = Utils.getPointers(rules);
      addRules(pointer, ntSymbol.getPointer(), pointers);
    }

    public native void addRules(long pointer, long ntSymbolPointer, long [] rulePointers);

    /**
     * Allow \p ntSymbol to be an arbitrary constant.
     * @param ntSymbol the non-terminal allowed to be any constant
     */
    void addAnyConstant(Term ntSymbol)
    {
      addAnyConstant(pointer, ntSymbol.getPointer());
    }

    private native void addAnyConstant(long pointer, long ntSymbolPointer);

    /**
     * Allow \p ntSymbol to be any input variable to corresponding
     * synth-fun/synth-inv with the same sort as \p ntSymbol.
     * @param ntSymbol the non-terminal allowed to be any input constant
     */
    void addAnyVariable(Term ntSymbol)
    {
      addAnyVariable(pointer, ntSymbol.getPointer());
    }

    private native void addAnyVariable(long pointer, long ntSymbolPointer);

    /**
     * @return a string representation of this grammar.
     */
  protected native String toString(long pointer);
}
