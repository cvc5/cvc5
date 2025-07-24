/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.util.Map;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.lang.Long;

public class Context
{
  // store pointers for terms, sorts, etc

  private static Map<Long, AbstractPointer> abstractPointers = new LinkedHashMap<>();

  static void addAbstractPointer(AbstractPointer pointer)
  {
    abstractPointers.put(Long.valueOf(pointer.getPointer()), pointer);
  }

  /**
   * Remove our record of a cpp pointer when it is deleted.
   */
  static void removeAbstractPointer(AbstractPointer pointer) {
    if (pointer.getPointer() != 0) {
      abstractPointers.remove(Long.valueOf(pointer.getPointer()));
    }
  }

  /**
   * Delete all cpp pointers for terms, sorts, etc
   */
  public static void deletePointers()
  {
    LinkedList<AbstractPointer> values = new LinkedList<AbstractPointer>(abstractPointers.values());
    Iterator<AbstractPointer> i = values.descendingIterator();
    while (i.hasNext()) {
      i.next().deletePointer();
    }

    abstractPointers.clear();
  }
}
