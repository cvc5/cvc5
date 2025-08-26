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

/**
 * A parser-related API exception.
 */
public class CVC5ParserException extends Exception
{
  /**
   * Construct with message from a string.
   *
   * @param message The error message.
   */
  public CVC5ParserException(String message)
  {
    super(message);
  }
}
