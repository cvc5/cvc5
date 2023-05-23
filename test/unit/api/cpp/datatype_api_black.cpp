/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the datatype classes of the C++ API.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackDatatype : public TestApi
{
};

TEST_F(TestApiBlackDatatype, mkDatatypeSort)
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
  ASSERT_THROW(d[2], CVC5ApiException);
  ASSERT_NO_THROW(consConstr.getTerm());
  ASSERT_NO_THROW(nilConstr.getTerm());
}

TEST_F(TestApiBlackDatatype, isNull)
{
  // creating empty (null) objects.
  DatatypeDecl dtypeSpec;
  DatatypeConstructorDecl cons;
  Datatype d;
  DatatypeConstructor consConstr;
  DatatypeSelector sel;

  // verifying that the objects are considered null.
  ASSERT_TRUE(dtypeSpec.isNull());
  ASSERT_TRUE(cons.isNull());
  ASSERT_TRUE(d.isNull());
  ASSERT_TRUE(consConstr.isNull());
  ASSERT_TRUE(sel.isNull());

  // changing the objects to be non-null
  dtypeSpec = d_solver.mkDatatypeDecl("list");
  cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  ASSERT_EQ(dtypeSpec.getNumConstructors(), 1);
  ASSERT_FALSE(dtypeSpec.isParametric());
  Sort listSort = d_solver.mkDatatypeSort(dtypeSpec);
  d = listSort.getDatatype();
  consConstr = d[0];
  sel = consConstr[0];

  // verifying that the new objects are non-null
  ASSERT_FALSE(dtypeSpec.isNull());
  ASSERT_FALSE(cons.isNull());
  ASSERT_FALSE(d.isNull());
  ASSERT_FALSE(consConstr.isNull());
  ASSERT_FALSE(sel.isNull());

  {
    std::stringstream ss;
    ss << cons;
    ASSERT_EQ(ss.str(), cons.toString());
  }
  {
    std::stringstream ss;
    ss << sel;
    ASSERT_EQ(ss.str(), sel.toString());
  }
  {
    std::stringstream ss;
    ss << consConstr;
    ASSERT_EQ(ss.str(), consConstr.toString());
  }
  {
    std::stringstream ss;
    ss << d;
    ASSERT_EQ(ss.str(), d.toString());
  }

  {
    Datatype::const_iterator it;
    it = d.begin();
    ASSERT_TRUE(it != d.end());
    ASSERT_FALSE(it->isNull());
    ASSERT_FALSE((*it).isNull());
    auto tmp = it;
    tmp++;
    ASSERT_EQ(tmp, d.end());
    tmp = it;
    ++tmp;
    ASSERT_EQ(tmp, d.end());
  }

  {
    DatatypeConstructor::const_iterator it;
    it = consConstr.begin();
    ASSERT_TRUE(it != consConstr.end());
    ASSERT_FALSE(it->isNull());
    ASSERT_FALSE((*it).isNull());
    auto tmp = it;
    tmp++;
    ASSERT_EQ(tmp, consConstr.end());
    tmp = it;
    ++tmp;
    ASSERT_EQ(tmp, consConstr.end());
  }
}

TEST_F(TestApiBlackDatatype, mkDatatypeSorts)
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
  Sort unresTree = d_solver.mkUnresolvedDatatypeSort("tree");
  Sort unresList = d_solver.mkUnresolvedDatatypeSort("list");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), dtdecls.size());
  for (size_t i = 0, ndecl = dtdecls.size(); i < ndecl; i++)
  {
    ASSERT_TRUE(dtsorts[i].isDatatype());
    ASSERT_FALSE(dtsorts[i].getDatatype().isFinite());
    ASSERT_EQ(dtsorts[i].getDatatype().getName(), dtdecls[i].getName());
  }
  // verify the resolution was correct
  Datatype dtTree = dtsorts[0].getDatatype();
  DatatypeConstructor dtcTreeNode = dtTree[0];
  ASSERT_EQ(dtcTreeNode.getName(), "node");
  DatatypeSelector dtsTreeNodeLeft = dtcTreeNode[0];
  ASSERT_EQ(dtsTreeNodeLeft.getName(), "left");
  // argument type should have resolved to be recursive
  ASSERT_TRUE(dtsTreeNodeLeft.getCodomainSort().isDatatype());
  ASSERT_EQ(dtsTreeNodeLeft.getCodomainSort(), dtsorts[0]);

  // fails due to empty datatype
  std::vector<DatatypeDecl> dtdeclsBad;
  DatatypeDecl emptyD = d_solver.mkDatatypeDecl("emptyD");
  dtdeclsBad.push_back(emptyD);
  ASSERT_THROW(d_solver.mkDatatypeSorts(dtdeclsBad), CVC5ApiException);
}

TEST_F(TestApiBlackDatatype, mkDatatypeSortsSelUnres)
{
  // Same as above, without unresolved sorts

  DatatypeDecl tree = d_solver.mkDatatypeDecl("tree");
  DatatypeConstructorDecl node = d_solver.mkDatatypeConstructorDecl("node");
  node.addSelectorUnresolved("left", "tree");
  node.addSelectorUnresolved("right", "tree");
  tree.addConstructor(node);

  DatatypeConstructorDecl leaf = d_solver.mkDatatypeConstructorDecl("leaf");
  leaf.addSelectorUnresolved("data", "list");
  tree.addConstructor(leaf);

  DatatypeDecl list = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelectorUnresolved("car", "tree");
  cons.addSelectorUnresolved("cdr", "tree");
  list.addConstructor(cons);

  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  list.addConstructor(nil);

  std::vector<DatatypeDecl> dtdecls;
  dtdecls.push_back(tree);
  dtdecls.push_back(list);
  std::vector<Sort> dtsorts;
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), dtdecls.size());
  for (size_t i = 0, ndecl = dtdecls.size(); i < ndecl; i++)
  {
    ASSERT_TRUE(dtsorts[i].isDatatype());
    ASSERT_FALSE(dtsorts[i].getDatatype().isFinite());
    ASSERT_EQ(dtsorts[i].getDatatype().getName(), dtdecls[i].getName());
  }
  // verify the resolution was correct
  Datatype dtTree = dtsorts[0].getDatatype();
  DatatypeConstructor dtcTreeNode = dtTree[0];
  ASSERT_EQ(dtcTreeNode.getName(), "node");
  DatatypeSelector dtsTreeNodeLeft = dtcTreeNode[0];
  ASSERT_EQ(dtsTreeNodeLeft.getName(), "left");
  // argument type should have resolved to be recursive
  ASSERT_TRUE(dtsTreeNodeLeft.getCodomainSort().isDatatype());
  ASSERT_EQ(dtsTreeNodeLeft.getCodomainSort(), dtsorts[0]);
}

TEST_F(TestApiBlackDatatype, datatypeStructs)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort boolSort = d_solver.getBooleanSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", intSort);
  cons.addSelectorSelf("tail");
  Sort nullSort;
  ASSERT_THROW(cons.addSelector("null", nullSort), CVC5ApiException);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  ASSERT_FALSE(dt.isCodatatype());
  ASSERT_FALSE(dt.isTuple());
  ASSERT_FALSE(dt.isRecord());
  ASSERT_FALSE(dt.isFinite());
  ASSERT_TRUE(dt.isWellFounded());
  // get constructor
  DatatypeConstructor dcons = dt[0];
  Term consTerm = dcons.getTerm();
  ASSERT_EQ(dcons.getNumSelectors(), 2);

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
  ASSERT_FALSE(dtEnum.isTuple());
  ASSERT_TRUE(dtEnum.isFinite());

  // create codatatype
  DatatypeDecl dtypeSpecStream = d_solver.mkDatatypeDecl("stream", true);
  DatatypeConstructorDecl consStream =
      d_solver.mkDatatypeConstructorDecl("cons");
  consStream.addSelector("head", intSort);
  consStream.addSelectorSelf("tail");
  dtypeSpecStream.addConstructor(consStream);
  Sort dtypeSortStream = d_solver.mkDatatypeSort(dtypeSpecStream);
  Datatype dtStream = dtypeSortStream.getDatatype();
  ASSERT_TRUE(dtStream.isCodatatype());
  ASSERT_FALSE(dtStream.isFinite());
  // codatatypes may be well-founded
  ASSERT_TRUE(dtStream.isWellFounded());

  // create tuple
  Sort tupSort = d_solver.mkTupleSort({boolSort});
  Datatype dtTuple = tupSort.getDatatype();
  ASSERT_TRUE(dtTuple.isTuple());
  ASSERT_FALSE(dtTuple.isRecord());
  ASSERT_TRUE(dtTuple.isFinite());
  ASSERT_TRUE(dtTuple.isWellFounded());

  // create record
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", boolSort), std::make_pair("i", intSort)};
  Sort recSort = d_solver.mkRecordSort(fields);
  ASSERT_TRUE(recSort.isDatatype());
  Datatype dtRecord = recSort.getDatatype();
  ASSERT_FALSE(dtRecord.isTuple());
  ASSERT_TRUE(dtRecord.isRecord());
  ASSERT_FALSE(dtRecord.isFinite());
  ASSERT_TRUE(dtRecord.isWellFounded());
}

TEST_F(TestApiBlackDatatype, datatypeNames)
{
  Sort intSort = d_solver.getIntegerSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  ASSERT_NO_THROW(dtypeSpec.getName());
  ASSERT_EQ(dtypeSpec.getName(), std::string("list"));
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", intSort);
  cons.addSelectorSelf("tail");
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  ASSERT_THROW(dt.getParameters(), CVC5ApiException);
  ASSERT_EQ(dt.getName(), std::string("list"));
  ASSERT_NO_THROW(dt.getConstructor("nil"));
  ASSERT_NO_THROW(dt["cons"]);
  ASSERT_THROW(dt.getConstructor("head"), CVC5ApiException);
  ASSERT_THROW(dt.getConstructor(""), CVC5ApiException);

  DatatypeConstructor dcons = dt[0];
  ASSERT_EQ(dcons.getName(), std::string("cons"));
  ASSERT_NO_THROW(dcons.getSelector("head"));
  ASSERT_NO_THROW(dcons["tail"]);
  ASSERT_THROW(dcons.getSelector("cons"), CVC5ApiException);

  // get selector
  DatatypeSelector dselTail = dcons[1];
  ASSERT_EQ(dselTail.getName(), std::string("tail"));
  ASSERT_EQ(dselTail.getCodomainSort(), dtypeSort);

  // get selector from datatype
  ASSERT_NO_THROW(dt.getSelector("head"));
  ASSERT_THROW(dt.getSelector("cons"), CVC5ApiException);

  // possible to construct null datatype declarations if not using solver
  ASSERT_THROW(DatatypeDecl().getName(), CVC5ApiException);
}

TEST_F(TestApiBlackDatatype, parametricDatatype)
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

  ASSERT_TRUE(pairType.getDatatype().isParametric());
  std::vector<Sort> dparams = pairType.getDatatype().getParameters();
  ASSERT_TRUE(dparams[0] == t1 && dparams[1] == t2);

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

  ASSERT_NE(pairIntInt, pairRealReal);
  ASSERT_NE(pairIntReal, pairRealReal);
  ASSERT_NE(pairRealInt, pairRealReal);
  ASSERT_NE(pairIntInt, pairIntReal);
  ASSERT_NE(pairIntInt, pairRealInt);
  ASSERT_NE(pairIntReal, pairRealInt);
}

TEST_F(TestApiBlackDatatype, isFinite)
{
  DatatypeDecl dtypedecl = d_solver.mkDatatypeDecl("dt", {});
  DatatypeConstructorDecl ctordecl = d_solver.mkDatatypeConstructorDecl("cons");
  ctordecl.addSelector("sel", d_solver.getBooleanSort());
  dtypedecl.addConstructor(ctordecl);
  Sort dtype = d_solver.mkDatatypeSort(dtypedecl);
  ASSERT_TRUE(dtype.getDatatype().isFinite());

  Sort p = d_solver.mkParamSort("p1");
  DatatypeDecl pdtypedecl = d_solver.mkDatatypeDecl("dt", {p});
  DatatypeConstructorDecl pctordecl =
      d_solver.mkDatatypeConstructorDecl("cons");
  pctordecl.addSelector("sel", p);
  pdtypedecl.addConstructor(pctordecl);
  Sort pdtype = d_solver.mkDatatypeSort(pdtypedecl);
  ASSERT_THROW(pdtype.getDatatype().isFinite(), CVC5ApiException);
}

TEST_F(TestApiBlackDatatype, datatypeSimplyRec)
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
  Sort unresWList = d_solver.mkUnresolvedDatatypeSort("wlist");
  Sort unresList = d_solver.mkUnresolvedDatatypeSort("list");
  Sort unresNs = d_solver.mkUnresolvedDatatypeSort("ns");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 3);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[1].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[2].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     ns2 = elem2(ndata: array(int,ns2)) | nil2
   *   END;
   */
  Sort unresNs2 = d_solver.mkUnresolvedDatatypeSort("ns2");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 1);
  ASSERT_TRUE(dtsorts[0].getDatatype()[0][0].getCodomainSort().isArray());
  ASSERT_EQ(
      dtsorts[0].getDatatype()[0][0].getCodomainSort().getArrayElementSort(),
      dtsorts[0]);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list3 = cons3(car: ns3, cdr: list3) | nil3,
   *     ns3 = elem3(ndata: set(list3))
   *   END;
   */
  Sort unresNs3 = d_solver.mkUnresolvedDatatypeSort("ns3");
  Sort unresList3 = d_solver.mkUnresolvedDatatypeSort("list3");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 2);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[1].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list4 = cons(car: set(ns4), cdr: list4) | nil,
   *     ns4 = elem(ndata: list4)
   *   END;
   */
  Sort unresNs4 = d_solver.mkUnresolvedDatatypeSort("ns4");
  Sort unresList4 = d_solver.mkUnresolvedDatatypeSort("list4");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 2);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[1].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
   *   END;
   */
  Sort unresList5 = d_solver.mkUninterpretedSortConstructorSort(1, "list5");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 1);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
}

TEST_F(TestApiBlackDatatype, datatypeSpecializedCons)
{
  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     plist[X] = pcons(car: X, cdr: plist[X]) | pnil
   *   END;
   */
  // Make unresolved types as placeholders
  Sort unresList = d_solver.mkUninterpretedSortConstructorSort(1, "plist");

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
  ASSERT_NO_THROW(dtsorts = d_solver.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 1);
  Datatype d = dtsorts[0].getDatatype();
  DatatypeConstructor nilc = d[0];

  Sort isort = d_solver.getIntegerSort();
  std::vector<Sort> iargs;
  iargs.push_back(isort);
  Sort listInt = dtsorts[0].instantiate(iargs);

  std::vector<Sort> liparams = listInt.getDatatype().getParameters();
  // the parameter of the datatype is not instantiated
  ASSERT_TRUE(liparams.size() == 1 && liparams[0] == x);

  Term testConsTerm;
  // get the specialized constructor term for list[Int]
  ASSERT_NO_THROW(testConsTerm = nilc.getInstantiatedTerm(listInt));
  ASSERT_NE(testConsTerm, nilc.getTerm());
  // error to get the specialized constructor term for Int
  ASSERT_THROW(nilc.getInstantiatedTerm(isort), CVC5ApiException);
}
}  // namespace test
}  // namespace cvc5::internal
