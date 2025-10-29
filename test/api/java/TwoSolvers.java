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
 * A simple test of multiple SmtEngines.
 */

import io.github.cvc5.*;

public class TwoSolvers
{
  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver s1 = new Solver(tm);
    Solver s2 = new Solver(tm);

    Result res1 = s1.checkSatAssuming(tm.mkBoolean(false));
    Result res2 = s2.checkSatAssuming(tm.mkBoolean(false));

    int exitCode = (res1.isUnsat() && res2.isUnsat()) ? 0 : 1;
    System.exit(exitCode);
  }
}
