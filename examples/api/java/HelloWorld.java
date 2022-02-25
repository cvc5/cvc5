/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A very simple CVC5 tutorial example.
 */

import io.github.cvc5.api.*;

public class HelloWorld
{
  public static void main(String[] args)
  {
    try (Solver slv = new Solver())
    {
      Term helloworld = slv.mkConst(slv.getBooleanSort(), "Hello World!");

      System.out.println(helloworld + " is " + slv.checkEntailed(helloworld));
    }
  }
}
