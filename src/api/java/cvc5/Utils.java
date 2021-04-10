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
   * get pointers from one dimensional array
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

  /**
   * get pointers from two dimensional matrix
   */
  public static long[] getPointers(IPointer[][] objects)
  {
    long[][] pointers = new long[objects.length][];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = new long[objects[i].length];
      for(int j = 0; j < bound_vars[i].length; j++)
      {
        pointers[i][j] = objects[i][j].getPointer();
      }
    }
    return pointers;
  }

  public validateUnsigned(int integer, String name)
  {
    if(integer < 0)
    {
      throw new CVC5ApiException("Expected "+name+" '" + integer + "' to be non negative.");
    }
  }

  public validateUnsigned(long integer, String name)
  {
    if(integer < 0)
    {
      throw new CVC5ApiException("Expected "+name+" '" + integer + "' to be non negative.");
    }
  }
}
