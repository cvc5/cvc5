/*********************                                                        */
/*! \file datatype_api_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the datatype classes of the C++ API.
 **
 ** Black box testing of the datatype classes of the C++ API.
 **/

#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiDatatypeBlack : public TestApi
{
};

TEST_F(TestApiDatatypeBlack, mkDatatypeSort)
{
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort listSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype d = listSort.getDatatype();
  DatatypeConstructor consConstr = d[0];
  DatatypeConstructor nilConstr = d[1];
  EXPECT_THROW(d[2], CVC4ApiException);
  ASSERT_NO_THROW(consConstr.getConstructorTerm());
  ASSERT_NO_THROW(nilConstr.getConstructorTerm());
}

TEST_F(TestApiDatatypeBlack, mkDatatypeSorts)
{
  /* Create two mutual datatypes corresponding to this definition
   * block:
   *
   *   DATATYPE
   *     tree = node(left: tree, right: tree) | leaf(data: list),
   *     list = cons(car: tree, cdr: list) | nil
   *   END;
   */
  // Make unresolved types as placeholders
  std::set<Sort> unresTypes;
  Sort unresTree = d_solver.mkUninterpretedSort("tree");
  Sort unresList = d_solver.mkUninterpretedSort("list");
  unresTypes.insert(unresTree);
  unresTypes.insert(unresList);

  DatatypeDecl tree = d_solver.mkDatatypeDecl("tree");
  DatatypeConstructorDecl node = d_solver.mkDatatypeConstructorDecl("node");
  node.addSelector("left", unresTree);
  node.addSelector("right", unresTree);
  tree.addConstructor(node);

  DatatypeConstructorDecl leaf = d_solver.mkDatatypeConstructorDecl("leaf");
  leaf.addSelector("data", unresList);
  tree.addConstructor(leaf);

  DatatypeDecl list = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("car", unresTree);
  cons.addSelector("cdr", unresTree);
  list.addConstructor(cons);

  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  list.addConstructor(nil);

  std::vector<DatatypeDecl> dtdecls;
  dtdecls.push_back(tree);
  dtdecls.push_back(list);
  std::vector<Sort> dtsorts;
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), dtdecls.size());
  for (size_t i = 0, ndecl = dtdecls.size(); i < ndecl; i++)
  {
    ASSERT_TRUE(dtsorts[i].isDatatype());
    EXPECT_FALSE(dtsorts[i].getDatatype().isFinite());
    EXPECT_EQ(dtsorts[i].getDatatype().getName(), dtdecls[i].getName());
  }
  // verify the resolution was correct
  Datatype dtTree = dtsorts[0].getDatatype();
  DatatypeConstructor dtcTreeNode = dtTree[0];
  EXPECT_EQ(dtcTreeNode.getName(), "node");
  DatatypeSelector dtsTreeNodeLeft = dtcTreeNode[0];
  EXPECT_EQ(dtsTreeNodeLeft.getName(), "left");
  // argument type should have resolved to be recursive
  EXPECT_TRUE(dtsTreeNodeLeft.getRangeSort().isDatatype());
  EXPECT_EQ(dtsTreeNodeLeft.getRangeSort(), dtsorts[0]);

  // fails due to empty datatype
  std::vector<DatatypeDecl> dtdeclsBad;
  DatatypeDecl emptyD = d_solver.mkDatatypeDecl("emptyD");
  dtdeclsBad.push_back(emptyD);
  EXPECT_THROW(d_solver.mkDatatypeSorts(dtdeclsBad), CVC4ApiException);
}

TEST_F(TestApiDatatypeBlack, datatypeStructs)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", intSort);
  cons.addSelectorSelf("tail");
  Sort nullSort;
  EXPECT_THROW(cons.addSelector("null", nullSort), CVC4ApiException);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  EXPECT_FALSE(dt.isCodatatype());
  EXPECT_FALSE(dt.isTuple());
  EXPECT_FALSE(dt.isRecord());
  EXPECT_FALSE(dt.isFinite());
  EXPECT_TRUE(dt.isWellFounded());
  // get constructor
  DatatypeConstructor dcons = dt[0];
  Term consTerm = dcons.getConstructorTerm();
  EXPECT_EQ(dcons.getNumSelectors(), 2);

  // create datatype sort to test
  DatatypeDecl dtypeSpecEnum = d_solver.mkDatatypeDecl("enum");
  DatatypeConstructorDecl ca = d_solver.mkDatatypeConstructorDecl("A");
  dtypeSpecEnum.addConstructor(ca);
  DatatypeConstructorDecl cb = d_solver.mkDatatypeConstructorDecl("B");
  dtypeSpecEnum.addConstructor(cb);
  DatatypeConstructorDecl cc = d_solver.mkDatatypeConstructorDecl("C");
  dtypeSpecEnum.addConstructor(cc);
  Sort dtypeSortEnum = d_solver.mkDatatypeSort(dtypeSpecEnum);
  Datatype dtEnum = dtypeSortEnum.getDatatype();
  EXPECT_FALSE(dtEnum.isTuple());
  EXPECT_TRUE(dtEnum.isFinite());

  // create codatatype
  DatatypeDecl dtypeSpecStream = d_solver.mkDatatypeDecl("stream", true);
  DatatypeConstructorDecl consStream =
      d_solver.mkDatatypeConstructorDecl("cons");
  consStream.addSelector("head", intSort);
  consStream.addSelectorSelf("tail");
  dtypeSpecStream.addConstructor(consStream);
  Sort dtypeSortStream = d_solver.mkDatatypeSort(dtypeSpecStream);
  Datatype dtStream = dtypeSortStream.getDatatype();
  EXPECT_TRUE(dtStream.isCodatatype());
  EXPECT_FALSE(dtStream.isFinite());
  // codatatypes may be well-founded
  EXPECT_TRUE(dtStream.isWellFounded());

  // create tuple
  Sort tupSort = d_solver.mkTupleSort({boolSort});
  Datatype dtTuple = tupSort.getDatatype();
  EXPECT_TRUE(dtTuple.isTuple());
  EXPECT_FALSE(dtTuple.isRecord());
  EXPECT_TRUE(dtTuple.isFinite());
  EXPECT_TRUE(dtTuple.isWellFounded());

  // create record
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", boolSort), std::make_pair("i", intSort)};
  Sort recSort = d_solver.mkRecordSort(fields);
  EXPECT_TRUE(recSort.isDatatype());
  Datatype dtRecord = recSort.getDatatype();
  EXPECT_FALSE(dtRecord.isTuple());
  EXPECT_TRUE(dtRecord.isRecord());
  EXPECT_FALSE(dtRecord.isFinite());
  EXPECT_TRUE(dtRecord.isWellFounded());
}

TEST_F(TestApiDatatypeBlack, datatypeNames)
{
  Sort intSort = d_solver.getIntegerSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  ASSERT_NO_THROW(dtypeSpec.getName());
  EXPECT_EQ(dtypeSpec.getName(), std::string("list"));
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", intSort);
  cons.addSelectorSelf("tail");
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  EXPECT_EQ(dt.getName(), std::string("list"));
  ASSERT_NO_THROW(dt.getConstructor("nil"));
  ASSERT_NO_THROW(dt["cons"]);
  ASSERT_THROW(dt.getConstructor("head"), CVC4ApiException);
  ASSERT_THROW(dt.getConstructor(""), CVC4ApiException);

  DatatypeConstructor dcons = dt[0];
  EXPECT_EQ(dcons.getName(), std::string("cons"));
  ASSERT_NO_THROW(dcons.getSelector("head"));
  ASSERT_NO_THROW(dcons["tail"]);
  ASSERT_THROW(dcons.getSelector("cons"), CVC4ApiException);

  // get selector
  DatatypeSelector dselTail = dcons[1];
  EXPECT_EQ(dselTail.getName(), std::string("tail"));
  EXPECT_EQ(dselTail.getRangeSort(), dtypeSort);

  // possible to construct null datatype declarations if not using solver
  ASSERT_THROW(DatatypeDecl().getName(), CVC4ApiException);
}

TEST_F(TestApiDatatypeBlack, parametricDatatype)
{
  std::vector<Sort> v;
  Sort t1 = d_solver.mkParamSort("T1");
  Sort t2 = d_solver.mkParamSort("T2");
  v.push_back(t1);
  v.push_back(t2);
  DatatypeDecl pairSpec = d_solver.mkDatatypeDecl("pair", v);

  DatatypeConstructorDecl mkpair =
      d_solver.mkDatatypeConstructorDecl("mk-pair");
  mkpair.addSelector("first", t1);
  mkpair.addSelector("second", t2);
  pairSpec.addConstructor(mkpair);

  Sort pairType = d_solver.mkDatatypeSort(pairSpec);

  EXPECT_TRUE(pairType.getDatatype().isParametric());

  v.clear();
  v.push_back(d_solver.getIntegerSort());
  v.push_back(d_solver.getIntegerSort());
  Sort pairIntInt = pairType.instantiate(v);
  v.clear();
  v.push_back(d_solver.getRealSort());
  v.push_back(d_solver.getRealSort());
  Sort pairRealReal = pairType.instantiate(v);
  v.clear();
  v.push_back(d_solver.getRealSort());
  v.push_back(d_solver.getIntegerSort());
  Sort pairRealInt = pairType.instantiate(v);
  v.clear();
  v.push_back(d_solver.getIntegerSort());
  v.push_back(d_solver.getRealSort());
  Sort pairIntReal = pairType.instantiate(v);

  EXPECT_NE(pairIntInt, pairRealReal);
  EXPECT_NE(pairIntReal, pairRealReal);
  EXPECT_NE(pairRealInt, pairRealReal);
  EXPECT_NE(pairIntInt, pairIntReal);
  EXPECT_NE(pairIntInt, pairRealInt);
  EXPECT_NE(pairIntReal, pairRealInt);

  EXPECT_TRUE(pairRealReal.isComparableTo(pairRealReal));
  EXPECT_FALSE(pairIntReal.isComparableTo(pairRealReal));
  EXPECT_FALSE(pairRealInt.isComparableTo(pairRealReal));
  EXPECT_FALSE(pairIntInt.isComparableTo(pairRealReal));
  EXPECT_FALSE(pairRealReal.isComparableTo(pairRealInt));
  EXPECT_FALSE(pairIntReal.isComparableTo(pairRealInt));
  EXPECT_TRUE(pairRealInt.isComparableTo(pairRealInt));
  EXPECT_FALSE(pairIntInt.isComparableTo(pairRealInt));
  EXPECT_FALSE(pairRealReal.isComparableTo(pairIntReal));
  EXPECT_TRUE(pairIntReal.isComparableTo(pairIntReal));
  EXPECT_FALSE(pairRealInt.isComparableTo(pairIntReal));
  EXPECT_FALSE(pairIntInt.isComparableTo(pairIntReal));
  EXPECT_FALSE(pairRealReal.isComparableTo(pairIntInt));
  EXPECT_FALSE(pairIntReal.isComparableTo(pairIntInt));
  EXPECT_FALSE(pairRealInt.isComparableTo(pairIntInt));
  EXPECT_TRUE(pairIntInt.isComparableTo(pairIntInt));

  EXPECT_TRUE(pairRealReal.isSubsortOf(pairRealReal));
  EXPECT_FALSE(pairIntReal.isSubsortOf(pairRealReal));
  EXPECT_FALSE(pairRealInt.isSubsortOf(pairRealReal));
  EXPECT_FALSE(pairIntInt.isSubsortOf(pairRealReal));
  EXPECT_FALSE(pairRealReal.isSubsortOf(pairRealInt));
  EXPECT_FALSE(pairIntReal.isSubsortOf(pairRealInt));
  EXPECT_TRUE(pairRealInt.isSubsortOf(pairRealInt));
  EXPECT_FALSE(pairIntInt.isSubsortOf(pairRealInt));
  EXPECT_FALSE(pairRealReal.isSubsortOf(pairIntReal));
  EXPECT_TRUE(pairIntReal.isSubsortOf(pairIntReal));
  EXPECT_FALSE(pairRealInt.isSubsortOf(pairIntReal));
  EXPECT_FALSE(pairIntInt.isSubsortOf(pairIntReal));
  EXPECT_FALSE(pairRealReal.isSubsortOf(pairIntInt));
  EXPECT_FALSE(pairIntReal.isSubsortOf(pairIntInt));
  EXPECT_FALSE(pairRealInt.isSubsortOf(pairIntInt));
  EXPECT_TRUE(pairIntInt.isSubsortOf(pairIntInt));
}

TEST_F(TestApiDatatypeBlack, datatypeSimplyRec)
{
  /* Create mutual datatypes corresponding to this definition block:
   *
   *   DATATYPE
   *     wlist = leaf(data: list),
   *     list = cons(car: wlist, cdr: list) | nil,
   *     ns = elem(ndata: set(wlist)) | elemArray(ndata2: array(list, list))
   *   END;
   */
  // Make unresolved types as placeholders
  std::set<Sort> unresTypes;
  Sort unresWList = d_solver.mkUninterpretedSort("wlist");
  Sort unresList = d_solver.mkUninterpretedSort("list");
  Sort unresNs = d_solver.mkUninterpretedSort("ns");
  unresTypes.insert(unresWList);
  unresTypes.insert(unresList);
  unresTypes.insert(unresNs);

  DatatypeDecl wlist = d_solver.mkDatatypeDecl("wlist");
  DatatypeConstructorDecl leaf = d_solver.mkDatatypeConstructorDecl("leaf");
  leaf.addSelector("data", unresList);
  wlist.addConstructor(leaf);

  DatatypeDecl list = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("car", unresWList);
  cons.addSelector("cdr", unresList);
  list.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  list.addConstructor(nil);

  DatatypeDecl ns = d_solver.mkDatatypeDecl("ns");
  DatatypeConstructorDecl elem = d_solver.mkDatatypeConstructorDecl("elem");
  elem.addSelector("ndata", d_solver.mkSetSort(unresWList));
  ns.addConstructor(elem);
  DatatypeConstructorDecl elemArray =
      d_solver.mkDatatypeConstructorDecl("elemArray");
  elemArray.addSelector("ndata", d_solver.mkArraySort(unresList, unresList));
  ns.addConstructor(elemArray);

  std::vector<DatatypeDecl> dtdecls;
  dtdecls.push_back(wlist);
  dtdecls.push_back(list);
  dtdecls.push_back(ns);
  // this is well-founded and has no nested recursion
  std::vector<Sort> dtsorts;
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), 3);
  EXPECT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[1].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[2].getDatatype().isWellFounded());
  EXPECT_FALSE(dtsorts[0].getDatatype().hasNestedRecursion());
  EXPECT_FALSE(dtsorts[1].getDatatype().hasNestedRecursion());
  EXPECT_FALSE(dtsorts[2].getDatatype().hasNestedRecursion());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     ns2 = elem2(ndata: array(int,ns2)) | nil2
   *   END;
   */
  unresTypes.clear();
  Sort unresNs2 = d_solver.mkUninterpretedSort("ns2");
  unresTypes.insert(unresNs2);

  DatatypeDecl ns2 = d_solver.mkDatatypeDecl("ns2");
  DatatypeConstructorDecl elem2 = d_solver.mkDatatypeConstructorDecl("elem2");
  elem2.addSelector("ndata",
                    d_solver.mkArraySort(d_solver.getIntegerSort(), unresNs2));
  ns2.addConstructor(elem2);
  DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil2");
  ns2.addConstructor(nil2);

  dtdecls.clear();
  dtdecls.push_back(ns2);

  dtsorts.clear();
  // this is not well-founded due to non-simple recursion
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), 1);
  ASSERT_TRUE(dtsorts[0].getDatatype()[0][0].getRangeSort().isArray());
  EXPECT_EQ(dtsorts[0].getDatatype()[0][0].getRangeSort().getArrayElementSort(),
            dtsorts[0]);
  EXPECT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[0].getDatatype().hasNestedRecursion());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list3 = cons3(car: ns3, cdr: list3) | nil3,
   *     ns3 = elem3(ndata: set(list3))
   *   END;
   */
  unresTypes.clear();
  Sort unresNs3 = d_solver.mkUninterpretedSort("ns3");
  unresTypes.insert(unresNs3);
  Sort unresList3 = d_solver.mkUninterpretedSort("list3");
  unresTypes.insert(unresList3);

  DatatypeDecl list3 = d_solver.mkDatatypeDecl("list3");
  DatatypeConstructorDecl cons3 = d_solver.mkDatatypeConstructorDecl("cons3");
  cons3.addSelector("car", unresNs3);
  cons3.addSelector("cdr", unresList3);
  list3.addConstructor(cons3);
  DatatypeConstructorDecl nil3 = d_solver.mkDatatypeConstructorDecl("nil3");
  list3.addConstructor(nil3);

  DatatypeDecl ns3 = d_solver.mkDatatypeDecl("ns3");
  DatatypeConstructorDecl elem3 = d_solver.mkDatatypeConstructorDecl("elem3");
  elem3.addSelector("ndata", d_solver.mkSetSort(unresList3));
  ns3.addConstructor(elem3);

  dtdecls.clear();
  dtdecls.push_back(list3);
  dtdecls.push_back(ns3);

  dtsorts.clear();
  // both are well-founded and have nested recursion
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), 2);
  EXPECT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[1].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[0].getDatatype().hasNestedRecursion());
  EXPECT_TRUE(dtsorts[1].getDatatype().hasNestedRecursion());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list4 = cons(car: set(ns4), cdr: list4) | nil,
   *     ns4 = elem(ndata: list4)
   *   END;
   */
  unresTypes.clear();
  Sort unresNs4 = d_solver.mkUninterpretedSort("ns4");
  unresTypes.insert(unresNs4);
  Sort unresList4 = d_solver.mkUninterpretedSort("list4");
  unresTypes.insert(unresList4);

  DatatypeDecl list4 = d_solver.mkDatatypeDecl("list4");
  DatatypeConstructorDecl cons4 = d_solver.mkDatatypeConstructorDecl("cons4");
  cons4.addSelector("car", d_solver.mkSetSort(unresNs4));
  cons4.addSelector("cdr", unresList4);
  list4.addConstructor(cons4);
  DatatypeConstructorDecl nil4 = d_solver.mkDatatypeConstructorDecl("nil4");
  list4.addConstructor(nil4);

  DatatypeDecl ns4 = d_solver.mkDatatypeDecl("ns4");
  DatatypeConstructorDecl elem4 = d_solver.mkDatatypeConstructorDecl("elem3");
  elem4.addSelector("ndata", unresList4);
  ns4.addConstructor(elem4);

  dtdecls.clear();
  dtdecls.push_back(list4);
  dtdecls.push_back(ns4);

  dtsorts.clear();
  // both are well-founded and have nested recursion
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), 2);
  EXPECT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[1].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[0].getDatatype().hasNestedRecursion());
  EXPECT_TRUE(dtsorts[1].getDatatype().hasNestedRecursion());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
   *   END;
   */
  unresTypes.clear();
  Sort unresList5 = d_solver.mkSortConstructorSort("list5", 1);
  unresTypes.insert(unresList5);

  std::vector<Sort> v;
  Sort x = d_solver.mkParamSort("X");
  v.push_back(x);
  DatatypeDecl list5 = d_solver.mkDatatypeDecl("list5", v);

  std::vector<Sort> args;
  args.push_back(x);
  Sort urListX = unresList5.instantiate(args);
  args[0] = urListX;
  Sort urListListX = unresList5.instantiate(args);

  DatatypeConstructorDecl cons5 = d_solver.mkDatatypeConstructorDecl("cons5");
  cons5.addSelector("car", x);
  cons5.addSelector("cdr", urListListX);
  list5.addConstructor(cons5);
  DatatypeConstructorDecl nil5 = d_solver.mkDatatypeConstructorDecl("nil5");
  list5.addConstructor(nil5);

  dtdecls.clear();
  dtdecls.push_back(list5);

  // well-founded and has nested recursion
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), 1);
  EXPECT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  EXPECT_TRUE(dtsorts[0].getDatatype().hasNestedRecursion());
}

TEST_F(TestApiDatatypeBlack, datatypeSpecializedCons)
{
  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     plist[X] = pcons(car: X, cdr: plist[X]) | pnil
   *   END;
   */
  // Make unresolved types as placeholders
  std::set<Sort> unresTypes;
  Sort unresList = d_solver.mkSortConstructorSort("plist", 1);
  unresTypes.insert(unresList);

  std::vector<Sort> v;
  Sort x = d_solver.mkParamSort("X");
  v.push_back(x);
  DatatypeDecl plist = d_solver.mkDatatypeDecl("plist", v);

  std::vector<Sort> args;
  args.push_back(x);
  Sort urListX = unresList.instantiate(args);

  DatatypeConstructorDecl pcons = d_solver.mkDatatypeConstructorDecl("pcons");
  pcons.addSelector("car", x);
  pcons.addSelector("cdr", urListX);
  plist.addConstructor(pcons);
  DatatypeConstructorDecl nil5 = d_solver.mkDatatypeConstructorDecl("pnil");
  plist.addConstructor(nil5);

  std::vector<DatatypeDecl> dtdecls;
  dtdecls.push_back(plist);

  std::vector<Sort> dtsorts;
  // make the datatype sorts
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls, unresTypes));
  ASSERT_EQ(dtsorts.size(), 1);
  Datatype d = dtsorts[0].getDatatype();
  DatatypeConstructor nilc = d[0];

  Sort isort = d_solver.getIntegerSort();
  std::vector<Sort> iargs;
  iargs.push_back(isort);
  Sort listInt = dtsorts[0].instantiate(iargs);

  Term testConsTerm;
  // get the specialized constructor term for list[Int]
  ASSERT_NO_THROW(testConsTerm = nilc.getSpecializedConstructorTerm(listInt));
  EXPECT_NE(testConsTerm, nilc.getConstructorTerm());
  // error to get the specialized constructor term for Int
  EXPECT_THROW(nilc.getSpecializedConstructorTerm(isort), CVC4ApiException);
}
}  // namespace test
}  // namespace CVC4
