/*********************                                                        */
/*! \file datatypes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An example of using inductive datatypes in CVC4
 **
 ** An example of using inductive datatypes in CVC4.
 **/

#include <iostream>

#include <cvc4/cvc4.h>

using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);

  // This example builds a simple "cons list" of integers, with
  // two constructors, "cons" and "nil."

  // Building a datatype consists of two steps.  First, the datatype
  // is specified.  Second, it is "resolved"---at which point function
  // symbols are assigned to its constructors, selectors, and testers.

  Datatype consListSpec("list"); // give the datatype a name
  DatatypeConstructor cons("cons");
  cons.addArg("head", em.integerType());
  cons.addArg("tail", DatatypeSelfType()); // a list
  consListSpec.addConstructor(cons);
  DatatypeConstructor nil("nil");
  consListSpec.addConstructor(nil);

  std::cout << "spec is:" << std::endl
            << consListSpec << std::endl;

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

  const Datatype& consList = consListType.getDatatype();

  // e = cons 0 nil
  //
  // Here, consList["cons"] gives you the DatatypeConstructor.  To get
  // the constructor symbol for application, use .getConstructor("cons"),
  // which is equivalent to consList["cons"].getConstructor().  Note that
  // "nil" is a constructor too, so it needs to be applied with
  // APPLY_CONSTRUCTOR, even though it has no arguments.
  Expr e = em.mkExpr(kind::APPLY_CONSTRUCTOR,
                     consList.getConstructor("cons"),
                     em.mkConst(Rational(0)),
                     em.mkExpr(kind::APPLY_CONSTRUCTOR,
                               consList.getConstructor("nil")));

  std::cout << "e is " << e << std::endl
            << "type of cons is " << consList.getConstructor("cons").getType()
            << std::endl
            << "type of nil is " << consList.getConstructor("nil").getType()
            << std::endl;

  // e2 = head(cons 0 nil), and of course this can be evaluated
  //
  // Here we first get the DatatypeConstructor for cons (with
  // consList["cons"]) in order to get the "head" selector symbol
  // to apply.
  Expr e2 = em.mkExpr(kind::APPLY_SELECTOR,
                      consList["cons"].getSelector("head"),
                      e);

  std::cout << "e2 is " << e2 << std::endl
            << "simplify(e2) is " << smt.simplify(e2)
            << std::endl << std::endl;

  // You can also iterate over a Datatype to get all its constructors,
  // and over a DatatypeConstructor to get all its "args" (selectors)
  for(Datatype::iterator i = consList.begin(); i != consList.end(); ++i) {
    std::cout << "ctor: " << *i << std::endl;
    for(DatatypeConstructor::iterator j = (*i).begin(); j != (*i).end(); ++j) {
      std::cout << " + arg: " << *j << std::endl;
    }
  }
  std::cout << std::endl;

  // You can also define parameterized datatypes.
  // This example builds a simple parameterized list of sort T, with one
  // constructor "cons".
  Type sort = em.mkSort("T", ExprManager::SORT_FLAG_PLACEHOLDER);
  Datatype paramConsListSpec("list", std::vector<Type>{sort});
  DatatypeConstructor paramCons("cons");
  DatatypeConstructor paramNil("nil");
  paramCons.addArg("head", sort);
  paramCons.addArg("tail", DatatypeSelfType());
  paramConsListSpec.addConstructor(paramCons);
  paramConsListSpec.addConstructor(paramNil);

  DatatypeType paramConsListType = em.mkDatatypeType(paramConsListSpec);
  Type paramConsIntListType = paramConsListType.instantiate(std::vector<Type>{em.integerType()});

  Datatype paramConsList = paramConsListType.getDatatype();

  std::cout << "parameterized datatype sort is " << std::endl;
  for (const DatatypeConstructor& ctor : paramConsList)
  {
    std::cout << "ctor: " << ctor << std::endl;
    for (const DatatypeConstructorArg& stor : ctor)
    {
      std::cout << " + arg: " << stor << std::endl;
    }
  }

  Expr a = em.mkVar("a", paramConsIntListType);
  std::cout << "Expr " << a << " is of type " << a.getType() << std::endl;

  Expr head_a = em.mkExpr(
      kind::APPLY_SELECTOR,
      paramConsList["cons"].getSelector("head"),
      a);
  std::cout << "head_a is " << head_a << " of type " << head_a.getType() 
            << std::endl
            << "type of cons is "
            << paramConsList.getConstructor("cons").getType() << std::endl
            << std::endl;

  Expr assertion = em.mkExpr(kind::GT, head_a, em.mkConst(Rational(50)));
  std::cout << "Assert " << assertion << std::endl;
  smt.assertFormula(assertion);

  std::cout << "Expect sat." << std::endl;
  std::cout << "CVC4: " << smt.checkSat()<< std::endl;

  return 0;
}
