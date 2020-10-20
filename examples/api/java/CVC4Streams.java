/*********************                                                        */
/*! \file CVC4Streams.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Example of driving CVC4 parsing from Java streams
 **
 ** This example shows how CVC4 can be driven from Java streams.
 **/

import java.io.*;
import edu.stanford.CVC4.*;

public class CVC4Streams {
  public static void main(String[] args) throws IOException {
    System.loadLibrary("cvc4jni");
    ExprManager exprMgr = new ExprManager();
    SmtEngine smt = new SmtEngine(exprMgr);
    smt.setOption("output-language", new SExpr("smt2"));

    PipedOutputStream solverPipe = new PipedOutputStream();
    PrintWriter toSolver = new PrintWriter(solverPipe);
    PipedInputStream stream = new PipedInputStream(solverPipe);

    toSolver.println("(set-logic QF_LIA)");
    toSolver.println("(declare-fun x () Int)");
    toSolver.println("(assert (= x 5))");
    toSolver.println("(check-sat)");
    toSolver.flush();

    ParserBuilder pbuilder =
      new ParserBuilder(exprMgr, "<string 1>")
      .withInputLanguage(InputLanguage.INPUT_LANG_SMTLIB_V2)
      .withLineBufferedStreamInput((java.io.InputStream)stream);
    Parser parser = pbuilder.build();

    Command cmd;
    while((cmd = parser.nextCommand()) != null) {
      System.out.println(cmd);
      cmd.invoke(smt, System.out);
    }

    toSolver.println("(assert (= x 10))");
    toSolver.println("(check-sat)");
    toSolver.flush();

    while((cmd = parser.nextCommand()) != null) {
      System.out.println(cmd);
      cmd.invoke(smt, System.out);
    }
  }
}
