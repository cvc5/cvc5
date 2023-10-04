package io.github.cvc5;
public class SymbolManager extends AbstractPointer
{
  public SymbolManager(long pointer)
  {
    super(pointer);
  }
  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "InputParser.toString() is not supported in the cpp api");
  }
  protected native void deletePointer(long pointer);
}
