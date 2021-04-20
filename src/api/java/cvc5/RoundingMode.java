/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Abdalrhman Mohamed, Mudathir Mohamed
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

package cvc5;

public enum RoundingMode
{
  ROUND_NEAREST_TIES_TO_EVEN(0),
  ROUND_TOWARD_POSITIVE(1),
  ROUND_TOWARD_NEGATIVE(2),
  ROUND_TOWARD_ZERO(3),
  ROUND_NEAREST_TIES_TO_AWAY(4);

  private int value;

  private RoundingMode(int value)
  {
    this.value = value;
  }

  public int getValue()
  {
    return value;
  }
}
