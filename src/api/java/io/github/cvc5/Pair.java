/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
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

/**
 * A simple generic container class to hold a pair of objects.
 *
 * @param <K> the type of the first element
 * @param <V> the type of the second element
 */
public class Pair<K, V>
{
  /**
   * The first element of the pair.
   */
  public K first;

  /**
   * The second element of the pair.
   */
  public V second;

  /**
   * Construct a new Pair with the given values.
   *
   * @param first  the first element of the pair
   * @param second the second element of the pair
   */
  public Pair(K first, V second)
  {
    this.first = first;
    this.second = second;
  }

  /**
   * Compare this Pair to the specified object for equality.
   *
   * It returns {@code true} if the given object is also a Pair and
   * both the first and second elements are equal (using their equals method).
   *
   * @param pair the object to compare with this pair
   * @return {@code true} if the specified object is equal to this pair,
   *         {@code false} otherwise
   */
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
