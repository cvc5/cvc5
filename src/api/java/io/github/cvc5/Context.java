/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.util.ArrayList;
import java.util.List;

public class Context
{
  // store pointers for terms, sorts, etc
  private static List<AbstractPointer> abstractPointers = new ArrayList<>();

  static void addAbstractPointer(AbstractPointer pointer)
  {
    abstractPointers.add(pointer);
  }

  /**
   * Delete all cpp pointers for terms, sorts, etc
   */
  public static void deletePointers()
  {
    for (int i = abstractPointers.size() - 1; i >= 0; i--)
    {
      abstractPointers.get(i).deletePointer();
    }
    abstractPointers.clear();
  }
}
