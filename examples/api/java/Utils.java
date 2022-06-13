/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Abdalrhman Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility methods.
 */

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.util.ArrayList;
import java.util.List;

public class Utils
{
  /**
   * Get the string version of define-fun command.
   *
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
   *
   * @param terms the terms for which the synthesis solutions were retrieved
   * @param sols the synthesis solutions of the given terms
   */
  public static void printSynthSolutions(Term[] terms, Term[] sols) throws CVC5ApiException
  {
    System.out.println('(');
    for (int i = 0; i < terms.length; ++i)
    {
      List<Term> params = new ArrayList<>();
      Term body = sols[i];
      if (sols[i].getKind() == Kind.LAMBDA)
      {
        for (Term t : sols[i].getChild(0))
        {
          params.add(t);
        }
        body = sols[i].getChild(1);
      }
      System.out.println("  " + defineFunToString(terms[i], params.toArray(new Term[0]), body));
    }
    System.out.println(')');
  }
}
