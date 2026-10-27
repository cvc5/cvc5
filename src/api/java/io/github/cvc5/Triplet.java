/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.util.Objects;

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
   * Elements are compared with
   * {@link java.util.Objects#equals(Object, Object)}, so {@code null} elements
   * are permitted and compare equal to each other.
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

    return Objects.equals(this.first, ((Triplet<?, ?, ?>) object).first)
        && Objects.equals(this.second, ((Triplet<?, ?, ?>) object).second)
        && Objects.equals(this.third, ((Triplet<?, ?, ?>) object).third);
  }

  /**
   * Return a hash code value for this triplet.
   *
   * The hash code is derived from the hash codes of the {@code first},
   * {@code second} and {@code third} elements, so that triplets that are equal
   * according to {@link #equals(Object)} have the same hash code.
   *
   * @return a hash code value for this triplet
   */
  @Override
  public int hashCode()
  {
    return Objects.hash(first, second, third);
  }
}
