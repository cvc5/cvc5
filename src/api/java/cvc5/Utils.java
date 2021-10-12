/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
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

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

public class Utils
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
    Convert a rational string a/b to a pair of BigIntegers
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
     Convert a pair of BigIntegers to a rational string a/b
   */
  public static String getRational(Pair<BigInteger, BigInteger> pair)
  {
    return pair.first.toString() + "/" + pair.second.toString();
  }

  /**
   * Get the string version of define-fun command.
   * @param f the function to print
   * @param params the function parameters
   * @param body the function body
   * @return a string version of define-fun
   */
  private static String defineFunToString(Term f, Term[] params, Term body)
  {
    Sort sort = f.getSort();
    if (sort.isFunction())
    {
      sort = sort.getFunctionCodomainSort();
    }
    StringBuilder ss = new StringBuilder();
    ss.append("(define-fun ").append(f).append(" (");
    for (int i = 0; i < params.length; ++i)
    {
      if (i > 0)
      {
        ss.append(' ');
      }
      ss.append('(').append(params[i]).append(' ').append(params[i].getSort()).append(')');
    }
    ss.append(") ").append(sort).append(' ').append(body).append(')');
    return ss.toString();
  }

  /**
   * Print solutions for synthesis conjecture to the standard output stream.
   * @param terms the terms for which the synthesis solutions were retrieved
   * @param sols the synthesis solutions of the given terms
   */
  public static void printSynthSolutions(Term[] terms, Term[] sols) throws CVC5ApiException
  {
    System.out.println('(');

    for (int i = 0; i < terms.length; ++i)
    {
      List<Term> params = new ArrayList<>();
      Term body = null;
      if (sols[i].getKind() == Kind.LAMBDA)
      {
        for (Term t : sols[i].getChild(0))
        {
          params.add(t);
        }
        body = sols[i].getChild(1);
      }
      if (body != null)
      {
        System.out.println("  " + defineFunToString(terms[i], params.toArray(new Term[0]), body));
      }
    }
    System.out.println(')');
  }
}
