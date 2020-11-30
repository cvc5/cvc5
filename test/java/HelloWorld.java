/*********************                                                        */
/*! \file HelloWorld.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Pat Hawks, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

import static org.junit.Assert.assertEquals;

import edu.stanford.CVC4.*;
import org.junit.Before;
import org.junit.Test;

public class HelloWorld {
  static {
    System.loadLibrary("cvc4jni");
  }
  ExprManager em;
  SmtEngine smt;

  @Before
  public void initialize() {
    em = new ExprManager();
    smt = new SmtEngine(em);
  }

  @Test
  public void evaluatesExpression() {
    Expr helloworld = em.mkVar("Hello World!", em.booleanType());
    Result.Entailment expect = Result.Entailment.NOT_ENTAILED;
    Result.Entailment actual = smt.checkEntailed(helloworld).isEntailed();
    assertEquals(actual, expect);
  }
}
