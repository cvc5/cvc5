/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of using inductive datatypes in cvc5.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

void test(Solver& slv, Sort& consListSort)
{
  TermManager& tm = slv.getTermManager();

  // Now our old "consListSpec" is useless--the relevant information
  // has been copied out, so we can throw that spec away.  We can get
  // the complete spec for the datatype from the DatatypeSort, and
  // this Datatype object has constructor symbols (and others) filled in.

  const Datatype& consList = consListSort.getDatatype();

  // t = cons 0 nil
  //
  // Here, consList["cons"] gives you the DatatypeConstructor.  To get
  // the constructor symbol for application, use .getConstructor("cons"),
  // which is equivalent to consList["cons"].getConstructor().  Note that
  // "nil" is a constructor too, so it needs to be applied with
  // APPLY_CONSTRUCTOR, even though it has no arguments.
  Term t = tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                     {consList.getConstructor("cons").getTerm(),
                      tm.mkInteger(0),
                      tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                                {consList.getConstructor("nil").getTerm()})});

  std::cout << "t is " << t << std::endl
            << "sort of cons is "
            << consList.getConstructor("cons").getTerm().getSort() << std::endl
            << "sort of nil is "
            << consList.getConstructor("nil").getTerm().getSort() << std::endl;

  // t2 = head(cons 0 nil), and of course this can be evaluated
  //
  // Here we first get the DatatypeConstructor for cons (with
  // consList["cons"]) in order to get the "head" selector symbol
  // to apply.
  Term t2 = tm.mkTerm(Kind::APPLY_SELECTOR,
                      {consList["cons"].getSelector("head").getTerm(), t});

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

  // You can also define a tester term for constructor 'cons': (_ is cons)
  Term t_is_cons =
      tm.mkTerm(Kind::APPLY_TESTER, {consList["cons"].getTesterTerm(), t});
  std::cout << "t_is_cons is " << t_is_cons << std::endl << std::endl;
  slv.assertFormula(t_is_cons);
  // Updating t at 'head' with value 1 is defined as follows:
  Term t_updated = tm.mkTerm(
      Kind::APPLY_UPDATER,
      {consList["cons"]["head"].getUpdaterTerm(), t, tm.mkInteger(1)});
  std::cout << "t_updated is " << t_updated << std::endl << std::endl;
  slv.assertFormula(tm.mkTerm(Kind::DISTINCT, {t, t_updated}));

  // You can also define parameterized datatypes.
  // This example builds a simple parameterized list of sort T, with one
  // constructor "cons".
  Sort sort = tm.mkParamSort("T");
  DatatypeDecl paramConsListSpec =
      tm.mkDatatypeDecl("paramlist", {sort});  // give the datatype a name
  DatatypeConstructorDecl paramCons = tm.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl paramNil = tm.mkDatatypeConstructorDecl("nil");
  paramCons.addSelector("head", sort);
  paramCons.addSelectorSelf("tail");
  paramConsListSpec.addConstructor(paramCons);
  paramConsListSpec.addConstructor(paramNil);

  Sort paramConsListSort = tm.mkDatatypeSort(paramConsListSpec);
  Sort paramConsIntListSort =
      paramConsListSort.instantiate(std::vector<Sort>{tm.getIntegerSort()});

  const Datatype& paramConsList = paramConsListSort.getDatatype();

  std::cout << "parameterized datatype sort is" << std::endl;
  for (const DatatypeConstructor& ctor : paramConsList)
  {
    std::cout << "ctor: " << ctor << std::endl;
    for (const DatatypeSelector& stor : ctor)
    {
      std::cout << " + arg: " << stor << std::endl;
    }
  }

  Term a = tm.mkConst(paramConsIntListSort, "a");
  std::cout << "term " << a << " is of sort " << a.getSort() << std::endl;

  Term head_a =
      tm.mkTerm(Kind::APPLY_SELECTOR,
                {paramConsList["cons"].getSelector("head").getTerm(), a});
  std::cout << "head_a is " << head_a << " of sort " << head_a.getSort()
            << std::endl
            << "sort of cons is "
            << paramConsList.getConstructor("cons").getTerm().getSort()
            << std::endl
            << std::endl;

  Term assertion = tm.mkTerm(Kind::GT, {head_a, tm.mkInteger(50)});
  std::cout << "Assert " << assertion << std::endl;
  slv.assertFormula(assertion);
  std::cout << "Expect sat." << std::endl;
  std::cout << "cvc5: " << slv.checkSat() << std::endl;
}

int main()
{
  TermManager tm;
  Solver slv(tm);
  // This example builds a simple "cons list" of integers, with
  // two constructors, "cons" and "nil."

  // Building a datatype consists of two steps.
  // First, the datatype is specified.
  // Second, it is "resolved" to an actual sort, at which point function
  // symbols are assigned to its constructors, selectors, and testers.

  DatatypeDecl consListSpec =
      tm.mkDatatypeDecl("list");  // give the datatype a name
  DatatypeConstructorDecl cons = tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", tm.getIntegerSort());
  cons.addSelectorSelf("tail");
  consListSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = tm.mkDatatypeConstructorDecl("nil");
  consListSpec.addConstructor(nil);

  std::cout << "spec is:" << std::endl << consListSpec << std::endl;

  // Keep in mind that "DatatypeDecl" is the specification class for
  // datatypes---"DatatypeDecl" is not itself a cvc5 Sort.
  // Now that our Datatype is fully specified, we can get a Sort for it.
  // This step resolves the "SelfSort" reference and creates
  // symbols for all the constructors, etc.

  Sort consListSort = tm.mkDatatypeSort(consListSpec);

  test(slv, consListSort);

  std::cout << std::endl
            << ">>> Alternatively, use declareDatatype" << std::endl;
  std::cout << std::endl;

  DatatypeConstructorDecl cons2 = tm.mkDatatypeConstructorDecl("cons");
  cons2.addSelector("head", tm.getIntegerSort());
  cons2.addSelectorSelf("tail");
  DatatypeConstructorDecl nil2 = tm.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors = {cons2, nil2};
  Sort consListSort2 = slv.declareDatatype("list2", ctors);
  test(slv, consListSort2);

  return 0;
}
