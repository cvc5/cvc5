/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mudathir Mohamed
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

/** Default value, current value and choices of a mode option */
public class ModeInfo extends ValueInfo<String>
{
  private final String[] modes;

  public ModeInfo(String defaultValue, String currentValue, String[] modes)
  {
    super(defaultValue, currentValue);
    this.modes = modes;
  }
  public String[] getModes()
  {
    return modes;
  }
}