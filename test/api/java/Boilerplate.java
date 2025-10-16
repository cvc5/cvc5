/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple start-up/tear-down test for cvc5.
 *
 * This simple test just makes sure that the public interface is
 * minimally functional.  It is useful as a template to use for other
 * system tests.
 */

import io.github.cvc5.*;

public class Boilerplate
{
  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    Result r = slv.checkSatAssuming(tm.mkBoolean(false));
    if (r.isUnsat())
    {
      System.exit(0);
    }
    else
    {
      System.exit(1);
    }
  }
}