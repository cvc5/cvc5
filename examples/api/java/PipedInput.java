/*********************                                                        */
/*! \file PipedInput.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the input parsing capabilities of CVC4
 ** when used from Java
 **
 ** A simple demonstration of the input parsing capabilities of CVC4 when
 ** used from Java.
 **/

import edu.stanford.CVC4.*;
import java.io.*;

public class PipedInput {
  public static void main(String[] args) throws IOException {
    System.loadLibrary("cvc4jni");

    // Boilerplate setup for CVC4
    ExprManager exprMgr = new ExprManager();
    SmtEngine smt = new SmtEngine(exprMgr);
    smt.setOption("output-language", new SExpr("smt2"));

    // Set up a pair of connected Java streams
    PipedOutputStream solverPipe = new PipedOutputStream();
    PrintWriter toSolver = new PrintWriter(solverPipe);
    PipedInputStream stream = new PipedInputStream(solverPipe);

    // Write some things to CVC4's input stream, making sure to flush()
    toSolver.println("(set-logic QF_LIA)");
    toSolver.println("(declare-fun x () Int)");
    toSolver.println("(assert (= x 5))");
    toSolver.println("(check-sat)");
    toSolver.flush();

    // Set up the CVC4 parser
    ParserBuilder pbuilder =
      new ParserBuilder(exprMgr, "<string 1>")
      .withInputLanguage(InputLanguage.INPUT_LANG_SMTLIB_V2)
      .withLineBufferedStreamInput((java.io.InputStream)stream);
    Parser parser = pbuilder.build();

    // Read all the commands thus far
    Command cmd;
    while((cmd = parser.nextCommand()) != null) {
      System.out.println(cmd);
      cmd.invoke(smt, System.out);
    }

    // Write some more things to CVC4's input stream, making sure to flush()
    toSolver.println("(assert (= x 10))");
    toSolver.println("(check-sat)");
    toSolver.flush();

    // Read all the commands thus far
    while((cmd = parser.nextCommand()) != null) {
      System.out.println(cmd);
      cmd.invoke(smt, System.out);
    }
  }
}
