package cvc5;

public class DatatypeConstructorDecl extends AbstractPointer
{
  // region construction and destruction
  DatatypeConstructorDecl(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  @Override
  public void finalize()
  {
    deletePointer(pointer);
  }

  // endregion

  /**
   * Add datatype selector declaration.
   * @param name the name of the datatype selector declaration to add
   * @param sort the range sort of the datatype selector declaration to add
   */
  public void addSelector(String name, Sort sort)
  {
    addSelector(pointer, name, sort.getPointer());
  }

  private native void addSelector(long pointer, String name, long sortPointer);

  /**
   * Add datatype selector declaration whose range type is the datatype itself.
   * @param name the name of the datatype selector declaration to add
   */
  public void addSelectorSelf(String name)
  {
    addSelectorSelf(pointer, name);
  }

  private native void addSelectorSelf(long pointer, String name);

  /**
   * @return true if this DatatypeConstructorDecl is a null declaration.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return a string representation of this datatype constructor declaration
   */
  protected native String toString(long pointer);
}
