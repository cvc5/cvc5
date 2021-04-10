package cvc5;

import java.io.IOException;

class Utils
{
  static
  {
    loadLibraries();
  }

  /**
   * load cvc5 jni library
   */
  public static void loadLibraries()
  {
    System.loadLibrary("cvc5jni");
  }

  /**
   * return sorts array from array of pointers
   */
  public static Sort[] getSorts(Solver solver, long[] pointers)
  {
    Sort[] sorts = new Sort[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      sorts[i] = new Sort(solver, pointers[i]);
    }
    return sorts;
  }

  /**
   * return terms array from array of pointers
   */
  public static Term[] getTerms(Solver solver, long[] pointers)
  {
    Term[] terms = new Term[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      terms[i] = new Term(solver, pointers[i]);
    }
    return terms;
  }

  /**
   * @return c pointers that represent the given objects
   */
  public static long[] getPointers(IPointer[] objects)
  {
    long[] pointers = new long[objects.length];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = objects[i].getPointer();
    }
    return pointers;
  }
}
