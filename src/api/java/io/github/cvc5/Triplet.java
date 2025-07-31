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
 * A generic container class to hold a triplet of objects.
 *
 * @param <A> the type of the first element
 * @param <B> the type of the second element
 * @param <C> the type of the third element
 */
public class Triplet<A, B, C>
{
  /** The first element of the triplet. */
  public A first;

  /** The second element of the triplet. */
  public B second;

  /** The third element of the triplet. */
  public C third;

  /**
   * Construct a new {@code Triplet} with the specified values.
   *
   * @param first the first element
   * @param second the second element
   * @param third the third element
   */
  public Triplet(A first, B second, C third)
  {
    this.first = first;
    this.second = second;
    this.third = third;
  }

  /**
   * Indicate whether some other object is "equal to" this one.
   * Two {@code Triplet} instances are equal if their corresponding
   * {@code first}, {@code second}, and {@code third} elements are equal.
   *
   * @param object the object to compare with
   * @return {@code true} if this object is equal to the specified object;
   *         {@code false} otherwise
   */
  @Override
  public boolean equals(Object object)
  {
    if (this == object)
      return true;
    if (object == null || getClass() != object.getClass())
      return false;

    return this.first.equals(((Triplet<?, ?, ?>) object).first)
        && this.second.equals(((Triplet<?, ?, ?>) object).second)
        && this.third.equals(((Triplet<?, ?, ?>) object).third);
  }
}
