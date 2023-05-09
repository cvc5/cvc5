/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
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

public class Pair<K, V>
{
  public K first;
  public V second;
  public Pair(K first, V second)
  {
    this.first = first;
    this.second = second;
  }

  @Override
  public boolean equals(Object pair)
  {
    if (this == pair)
      return true;
    if (pair == null || getClass() != pair.getClass())
      return false;

    return first.equals(((Pair<?, ?>) pair).first) && second.equals(((Pair<?, ?>) pair).second);
  }
}
