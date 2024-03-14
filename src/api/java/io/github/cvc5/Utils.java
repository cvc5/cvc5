/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.math.BigInteger;

public class Utils
{
  static
  {
    loadLibraries();
  }

  /**
   * Load cvc5 jni library.
   */
  public static void loadLibraries()
  {
    if (!Boolean.parseBoolean(System.getProperty("cvc5.skipLibraryLoad")))
    {
      System.loadLibrary("cvc5jni");
    }
  }

  /**
   * @return Sorts array from array of Sort pointers.
   * @param pointers The array of pointers.
   */
  public static Sort[] getSorts(long[] pointers)
  {
    Sort[] sorts = new Sort[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      sorts[i] = new Sort(pointers[i]);
    }
    return sorts;
  }

  /**
   * @return Terms array from array of Term pointers.
   * @param pointers The array of pointers.
   */
  public static Term[] getTerms(long[] pointers)
  {
    Term[] terms = new Term[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      terms[i] = new Term(pointers[i]);
    }
    return terms;
  }

  /**
   * return proofs array from array of pointers
   */
  public static Proof[] getProofs(long[] pointers)
  {
    Proof[] proofs = new Proof[pointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      proofs[i] = new Proof(pointers[i]);
    }
    return proofs;
  }

  /**
   * @return Pointers from one dimensional array.
   * @param objects The one dimensional array of pointers.
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
   * @return Pointers from two dimensional matrix.
   * @param objects The two dimensional array of pointers.
   */
  public static long[][] getPointers(IPointer[][] objects)
  {
    long[][] pointers = new long[objects.length][];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = new long[objects[i].length];
      for (int j = 0; j < objects[i].length; j++)
      {
        pointers[i][j] = objects[i][j].getPointer();
      }
    }
    return pointers;
  }

  public static void validateUnsigned(int integer, String name) throws CVC5ApiException
  {
    if (integer < 0)
    {
      throw new CVC5ApiException("Expected " + name + " '" + integer + "' to be non negative.");
    }
  }

  public static void validateUnsigned(long integer, String name) throws CVC5ApiException
  {
    if (integer < 0)
    {
      throw new CVC5ApiException("Expected " + name + " '" + integer + "' to be non negative.");
    }
  }

  public static void validateUnsigned(int[] integers, String name) throws CVC5ApiException
  {
    for (int i = 0; i < integers.length; i++)
    {
      if (integers[i] < 0)
      {
        throw new CVC5ApiException(
            "Expected " + name + "[" + i + "] '" + integers[i] + "' to be non negative.");
      }
    }
  }

  public static void validateUnsigned(long[] integers, String name) throws CVC5ApiException
  {
    for (int i = 0; i < integers.length; i++)
    {
      if (integers[i] < 0)
      {
        throw new CVC5ApiException(
            "Expected " + name + "[" + i + "] '" + integers[i] + "' to be non negative.");
      }
    }
  }

  @SuppressWarnings("unchecked")
  public static <K> Pair<K, Long>[] getPairs(Pair<K, ? extends AbstractPointer>[] abstractPointers)
  {
    Pair<K, Long>[] pointers = new Pair[abstractPointers.length];
    for (int i = 0; i < pointers.length; i++)
    {
      pointers[i] = new Pair<>(abstractPointers[i].first, abstractPointers[i].second.getPointer());
    }
    return pointers;
  }

  /**
   * Convert a rational string a/b to a pair of BigIntegers
   * @return The pair of big integers.
   */
  public static Pair<BigInteger, BigInteger> getRational(String rational)
  {
    if (rational.contains("/"))
    {
      String[] pair = rational.split("/");
      return new Pair<>(new BigInteger(pair[0]), new BigInteger(pair[1]));
    }
    return new Pair<>(new BigInteger(rational), new BigInteger("1"));
  }

  /**
   * Convert a pair of BigIntegers to a rational string a/b
   * @return The rational string.
   */
  public static String getRational(Pair<BigInteger, BigInteger> pair)
  {
    return pair.first.toString() + "/" + pair.second.toString();
  }
}
