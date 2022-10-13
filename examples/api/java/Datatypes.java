/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of using inductive datatypes in cvc5.
 */

import io.github.cvc5.*;
import java.util.Iterator;

public class Datatypes
{
  private static void test(Solver slv, Sort consListSort) throws CVC5ApiException
  {
    // Now our old "consListSpec" is useless--the relevant information
    // has been copied out, so we can throw that spec away.  We can get
    // the complete spec for the datatype from the DatatypeSort, and
    // this Datatype object has constructor symbols (and others) filled in.

    Datatype consList = consListSort.getDatatype();

    // t = cons 0 nil
    //
    // Here, consList["cons"] gives you the DatatypeConstructor.  To get
    // the constructor symbol for application, use .getConstructor("cons"),
    // which is equivalent to consList["cons"].getConstructor().  Note that
    // "nil" is a constructor too, so it needs to be applied with
    // APPLY_CONSTRUCTOR, even though it has no arguments.
    Term t = slv.mkTerm(Kind.APPLY_CONSTRUCTOR,
        consList.getConstructor("cons").getTerm(),
        slv.mkInteger(0),
        slv.mkTerm(Kind.APPLY_CONSTRUCTOR, consList.getConstructor("nil").getTerm()));

    System.out.println("t is " + t + "\n"
        + "sort of cons is " + consList.getConstructor("cons").getTerm().getSort() + "\n"
        + "sort of nil is " + consList.getConstructor("nil").getTerm().getSort());

    // t2 = head(cons 0 nil), and of course this can be evaluated
    //
    // Here we first get the DatatypeConstructor for cons (with
    // consList["cons"]) in order to get the "head" selector symbol
    // to apply.
    Term t2 = slv.mkTerm(
        Kind.APPLY_SELECTOR, consList.getConstructor("cons").getSelector("head").getTerm(), t);

    System.out.println("t2 is " + t2 + "\n"
        + "simplify(t2) is " + slv.simplify(t2) + "\n");

    // You can also iterate over a Datatype to get all its constructors,
    // and over a DatatypeConstructor to get all its "args" (selectors)

    for (Iterator<DatatypeConstructor> i = consList.iterator(); i.hasNext();)
    {
      DatatypeConstructor constructor = i.next();
      System.out.println("ctor: " + constructor);
      for (Iterator<DatatypeSelector> j = constructor.iterator(); j.hasNext();)
      {
        System.out.println(" + arg: " + j.next());
      }
    }
    System.out.println();

    // Alternatively, you can use for each loops.
    for (DatatypeConstructor c : consList)
    {
      System.out.println("ctor: " + c);
      for (DatatypeSelector s : c)
      {
        System.out.println(" + arg: " + s);
      }
    }
    System.out.println();

    // You can also define a tester term for constructor 'cons': (_ is cons)
    Term t_is_cons =
        slv.mkTerm(Kind.APPLY_TESTER, consList.getConstructor("cons").getTesterTerm(), t);
    System.out.println("t_is_cons is " + t_is_cons + "\n");
    slv.assertFormula(t_is_cons);
    // Updating t at 'head' with value 1 is defined as follows:
    Term t_updated = slv.mkTerm(Kind.APPLY_UPDATER,
        consList.getConstructor("cons").getSelector("head").getUpdaterTerm(),
        t,
        slv.mkInteger(1));
    System.out.println("t_updated is " + t_updated + "\n");
    slv.assertFormula(slv.mkTerm(Kind.DISTINCT, t, t_updated));

    // You can also define parameterized datatypes.
    // This example builds a simple parameterized list of sort T, with one
    // constructor "cons".
    Sort sort = slv.mkParamSort("T");
    DatatypeDecl paramConsListSpec =
        slv.mkDatatypeDecl("paramlist", new Sort[] {sort}); // give the datatype a name
    DatatypeConstructorDecl paramCons = slv.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl paramNil = slv.mkDatatypeConstructorDecl("nil");
    paramCons.addSelector("head", sort);
    paramCons.addSelectorSelf("tail");
    paramConsListSpec.addConstructor(paramCons);
    paramConsListSpec.addConstructor(paramNil);

    Sort paramConsListSort = slv.mkDatatypeSort(paramConsListSpec);
    Sort paramConsIntListSort = paramConsListSort.instantiate(new Sort[] {slv.getIntegerSort()});

    Datatype paramConsList = paramConsListSort.getDatatype();

    System.out.println("parameterized datatype sort is ");
    for (DatatypeConstructor ctor : paramConsList)
    {
      System.out.println("ctor: " + ctor);
      for (DatatypeSelector stor : ctor)
      {
        System.out.println(" + arg: " + stor);
      }
    }

    Term a = slv.mkConst(paramConsIntListSort, "a");
    System.out.println("term " + a + " is of sort " + a.getSort());

    Term head_a = slv.mkTerm(
        Kind.APPLY_SELECTOR, paramConsList.getConstructor("cons").getSelector("head").getTerm(), a);
    System.out.println("head_a is " + head_a + " of sort " + head_a.getSort() + "\n"
        + "sort of cons is " + paramConsList.getConstructor("cons").getTerm().getSort() + "\n");
    Term assertion = slv.mkTerm(Kind.GT, head_a, slv.mkInteger(50));
    System.out.println("Assert " + assertion);
    slv.assertFormula(assertion);
    System.out.println("Expect sat.");
    System.out.println("cvc5: " + slv.checkSat());
  }

  public static void main(String[] args) throws CVC5ApiException
  {
    Solver slv = new Solver();
    {
      // This example builds a simple "cons list" of integers, with
      // two constructors, "cons" and "nil."

      // Building a datatype consists of two steps.
      // First, the datatype is specified.
      // Second, it is "resolved" to an actual sort, at which point function
      // symbols are assigned to its constructors, selectors, and testers.

      DatatypeDecl consListSpec = slv.mkDatatypeDecl("list"); // give the datatype a name
      DatatypeConstructorDecl cons = slv.mkDatatypeConstructorDecl("cons");
      cons.addSelector("head", slv.getIntegerSort());
      cons.addSelectorSelf("tail");
      consListSpec.addConstructor(cons);
      DatatypeConstructorDecl nil = slv.mkDatatypeConstructorDecl("nil");
      consListSpec.addConstructor(nil);

      System.out.println("spec is:"
          + "\n" + consListSpec);

      // Keep in mind that "DatatypeDecl" is the specification class for
      // datatypes---"DatatypeDecl" is not itself a cvc5 Sort.
      // Now that our Datatype is fully specified, we can get a Sort for it.
      // This step resolves the "SelfSort" reference and creates
      // symbols for all the constructors, etc.

      Sort consListSort = slv.mkDatatypeSort(consListSpec);

      test(slv, consListSort);

      System.out.println("\n"
          + ">>> Alternatively, use declareDatatype");
      System.out.println();

      DatatypeConstructorDecl cons2 = slv.mkDatatypeConstructorDecl("cons");
      cons2.addSelector("head", slv.getIntegerSort());
      cons2.addSelectorSelf("tail");
      DatatypeConstructorDecl nil2 = slv.mkDatatypeConstructorDecl("nil");
      DatatypeConstructorDecl[] ctors = new DatatypeConstructorDecl[] {cons2, nil2};
      Sort consListSort2 = slv.declareDatatype("list2", ctors);
      test(slv, consListSort2);
    }
  }
}
