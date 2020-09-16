/*********************                                                        */
/*! \file HelloWorld.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A very simple CVC4 example
 **
 ** A very simple CVC4 tutorial example.
 **/

import edu.stanford.CVC4.*;

public class HelloWorld {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    Expr helloworld = em.mkVar("Hello World!", em.booleanType());
    SmtEngine smt = new SmtEngine(em);

    System.out.println(helloworld + " is " + smt.checkEntailed(helloworld));
  }
}
