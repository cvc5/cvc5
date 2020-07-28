/*********************                                                        */
/*! \file Datatypes.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An example of using inductive datatypes in CVC4 (Java version)
 **
 ** An example of using inductive datatypes in CVC4 (Java version).
 **/

import edu.stanford.CVC4.*;
import java.util.Iterator;

public class Datatypes {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    // This example builds a simple "cons list" of integers, with
    // two constructors, "cons" and "nil."

    // Building a datatype consists of two steps.  First, the datatype
    // is specified.  Second, it is "resolved"---at which point function
    // symbols are assigned to its constructors, selectors, and testers.

    Datatype consListSpec = new Datatype(em, "list"); // give a name
    DatatypeConstructor cons = new DatatypeConstructor(em, "cons");
    cons.addArg("head", em.integerType());
    cons.addArg("tail", new DatatypeSelfType()); // a list
    consListSpec.addConstructor(cons);
    DatatypeConstructor nil = new DatatypeConstructor(em, "nil");
    consListSpec.addConstructor(nil);

    System.out.println("spec is:");
    System.out.println(consListSpec);

    // Keep in mind that "Datatype" is the specification class for
    // datatypes---"Datatype" is not itself a CVC4 Type.  Now that
    // our Datatype is fully specified, we can get a Type for it.
    // This step resolves the "SelfType" reference and creates
    // symbols for all the constructors, etc.

    DatatypeType consListType = em.mkDatatypeType(consListSpec);

    // Now our old "consListSpec" is useless--the relevant information
    // has been copied out, so we can throw that spec away.  We can get
    // the complete spec for the datatype from the DatatypeType, and
    // this Datatype object has constructor symbols (and others) filled in.

    Datatype consList = consListType.getDatatype();

    // e = cons 0 nil
    //
    // Here, consList.get("cons") gives you the DatatypeConstructor
    // (just as consList["cons"] does in C++).  To get the constructor
    // symbol for application, use .getConstructor("cons"), which is
    // equivalent to consList.get("cons").getConstructor().  Note that
    // "nil" is a constructor too, so it needs to be applied with
    // APPLY_CONSTRUCTOR, even though it has no arguments.
    Expr e = em.mkExpr(Kind.APPLY_CONSTRUCTOR,
                       consList.getConstructor("cons"),
                       em.mkConst(new Rational(0)),
                       em.mkExpr(Kind.APPLY_CONSTRUCTOR,
                                 consList.getConstructor("nil")));

    System.out.println("e is " + e);
    System.out.println("type of cons is " +
                       consList.getConstructor("cons").getType());
    System.out.println("type of nil is " +
                       consList.getConstructor("nil").getType());

    // e2 = head(cons 0 nil), and of course this can be evaluated
    //
    // Here we first get the DatatypeConstructor for cons (with
    // consList.get("cons") in order to get the "head" selector
    // symbol to apply.
    Expr e2 = em.mkExpr(Kind.APPLY_SELECTOR,
                        consList.get("cons").getSelector("head"),
                        e);

    System.out.println("e2 is " + e2);
    System.out.println("simplify(e2) is " + smt.simplify(e2));
    System.out.println();

    // You can also iterate over a Datatype to get all its constructors,
    // and over a DatatypeConstructor to get all its "args" (selectors)
    for(Iterator<DatatypeConstructor> i = consList.iterator(); i.hasNext();) {
      DatatypeConstructor ctor = i.next();
      System.out.println("ctor: " + ctor);
      for(Iterator j = ctor.iterator(); j.hasNext();) {
        System.out.println(" + arg: " + j.next());
      }
    }
  }
}
