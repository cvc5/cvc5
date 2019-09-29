/*********************                                                        */
/*! \file datatypes-new.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Makai Mann
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

#include <cvc4/api/cvc4cpp.h>

using namespace CVC4::api;

void test(Solver& slv, Sort& consListSort)
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
  Term t = slv.mkTerm(
      APPLY_CONSTRUCTOR,
      consList.getConstructorTerm("cons"),
      slv.mkReal(0),
      slv.mkTerm(APPLY_CONSTRUCTOR, consList.getConstructorTerm("nil")));

  std::cout << "t is " << t << std::endl
            << "sort of cons is "
            << consList.getConstructorTerm("cons").getSort() << std::endl
            << "sort of nil is " << consList.getConstructorTerm("nil").getSort()
            << std::endl;

  // t2 = head(cons 0 nil), and of course this can be evaluated
  //
  // Here we first get the DatatypeConstructor for cons (with
  // consList["cons"]) in order to get the "head" selector symbol
  // to apply.
  Term t2 =
      slv.mkTerm(APPLY_SELECTOR, consList["cons"].getSelectorTerm("head"), t);

  std::cout << "t2 is " << t2 << std::endl
            << "simplify(t2) is " << slv.simplify(t2) << std::endl
            << std::endl;

  // You can also iterate over a Datatype to get all its constructors,
  // and over a DatatypeConstructor to get all its "args" (selectors)
  for (Datatype::const_iterator i = consList.begin(); i != consList.end(); ++i)
  {
    std::cout << "ctor: " << *i << std::endl;
    for (DatatypeConstructor::const_iterator j = (*i).begin(); j != (*i).end();
         ++j)
    {
      std::cout << " + arg: " << *j << std::endl;
    }
  }
  std::cout << std::endl;

  // Alternatively, you can use for each loops.
  for (const auto& c : consList)
  {
    std::cout << "ctor: " << c << std::endl;
    for (const auto& s : c)
    {
      std::cout << " + arg: " << s << std::endl;
    }
  }
  std::cout << std::endl;

  // You can also define parameterized datatypes.
  // This example builds a simple parameterized list of sort T, with one
  // constructor "cons".
  Sort sort = slv.mkParamSort("T");
  DatatypeDecl paramConsListSpec("paramlist",
                                 sort);  // give the datatype a name
  DatatypeConstructorDecl paramCons("cons");
  DatatypeConstructorDecl paramNil("nil");
  DatatypeSelectorDecl paramHead("head", sort);
  DatatypeSelectorDecl paramTail("tail", DatatypeDeclSelfSort());
  paramCons.addSelector(paramHead);
  paramCons.addSelector(paramTail);
  paramConsListSpec.addConstructor(paramCons);
  paramConsListSpec.addConstructor(paramNil);

  Sort paramConsListSort = slv.mkDatatypeSort(paramConsListSpec);
  Sort paramConsIntListSort =
      paramConsListSort.instantiate(std::vector<Sort>{slv.getIntegerSort()});

  Datatype paramConsList = paramConsListSort.getDatatype();

  std::cout << "parameterized datatype sort is " << std::endl;
  for (const DatatypeConstructor& ctor : paramConsList)
  {
    std::cout << "ctor: " << ctor << std::endl;
    for (const DatatypeSelector& stor : ctor)
    {
      std::cout << " + arg: " << stor << std::endl;
    }
  }

  Term a = slv.mkConst(paramConsIntListSort, "a");
  std::cout << "term " << a << " is of sort " << a.getSort() << std::endl;

  Term head_a = slv.mkTerm(
      APPLY_SELECTOR, paramConsList["cons"].getSelectorTerm("head"), a);
  std::cout << "head_a is " << head_a << " of sort " << head_a.getSort()
            << std::endl
            << "sort of cons is "
            << paramConsList.getConstructorTerm("cons").getSort() << std::endl
            << std::endl;
  Term assertion = slv.mkTerm(GT, head_a, slv.mkReal(50));
  std::cout << "Assert " << assertion << std::endl;
  slv.assertFormula(assertion);
  std::cout << "Expect sat." << std::endl;
  std::cout << "CVC4: " << slv.checkSat() << std::endl;
}

int main()
{
  Solver slv;
  // This example builds a simple "cons list" of integers, with
  // two constructors, "cons" and "nil."

  // Building a datatype consists of two steps.
  // First, the datatype is specified.
  // Second, it is "resolved" to an actual sort, at which point function
  // symbols are assigned to its constructors, selectors, and testers.

  DatatypeDecl consListSpec("list");  // give the datatype a name
  DatatypeConstructorDecl cons("cons");
  DatatypeSelectorDecl head("head", slv.getIntegerSort());
  DatatypeSelectorDecl tail("tail", DatatypeDeclSelfSort());
  cons.addSelector(head);
  cons.addSelector(tail);
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil("nil");
  consListSpec.addConstructor(nil);

  std::cout << "spec is:" << std::endl << consListSpec << std::endl;

  // Keep in mind that "DatatypeDecl" is the specification class for
  // datatypes---"DatatypeDecl" is not itself a CVC4 Sort.
  // Now that our Datatype is fully specified, we can get a Sort for it.
  // This step resolves the "SelfSort" reference and creates
  // symbols for all the constructors, etc.

  Sort consListSort = slv.mkDatatypeSort(consListSpec);

  test(slv, consListSort);

  std::cout << std::endl
            << ">>> Alternatively, use declareDatatype" << std::endl;
  std::cout << std::endl;

  std::vector<DatatypeConstructorDecl> ctors = {cons, nil};
  Sort consListSort2 = slv.declareDatatype("list2", ctors);
  test(slv, consListSort2);

  return 0;
}
