/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort listSort = d_tm.mkDatatypeSort(dtypeSpec);
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
  dtypeSpec = d_tm.mkDatatypeDecl("list");
  cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  ASSERT_EQ(dtypeSpec.getNumConstructors(), 1);
  ASSERT_FALSE(dtypeSpec.isParametric());
  Sort listSort = d_tm.mkDatatypeSort(dtypeSpec);
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
    ss << dtypeSpec;
    ASSERT_EQ(ss.str(), dtypeSpec.toString());
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

TEST_F(TestApiBlackDatatype, equalHash)
{
  DatatypeDecl decl1 = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons1 = d_tm.mkDatatypeConstructorDecl("cons");
  cons1.addSelector("head", d_tm.getIntegerSort());
  decl1.addConstructor(cons1);
  DatatypeConstructorDecl nil1 = d_tm.mkDatatypeConstructorDecl("nil");
  decl1.addConstructor(nil1);
  Sort list1 = d_tm.mkDatatypeSort(decl1);
  Datatype dt1 = list1.getDatatype();
  DatatypeConstructor consConstr1 = dt1[0];
  DatatypeConstructor nilConstr1 = dt1[1];
  DatatypeSelector head1 = consConstr1.getSelector("head");

  DatatypeDecl decl2 = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons2 = d_tm.mkDatatypeConstructorDecl("cons");
  cons2.addSelector("head", d_tm.getIntegerSort());
  decl2.addConstructor(cons2);
  DatatypeConstructorDecl nil2 = d_tm.mkDatatypeConstructorDecl("nil");
  decl2.addConstructor(nil2);
  Sort list2 = d_tm.mkDatatypeSort(decl2);
  Datatype dt2 = list2.getDatatype();
  DatatypeConstructor consConstr2 = dt2[0];
  DatatypeConstructor nilConstr2 = dt2[1];
  DatatypeSelector head2 = consConstr2.getSelector("head");

  ASSERT_EQ(decl1, decl1);
  ASSERT_FALSE(decl1 == decl2);
  ASSERT_EQ(cons1, cons1);
  ASSERT_FALSE(cons1 == cons2);
  ASSERT_EQ(nil1, nil1);
  ASSERT_FALSE(nil1 == nil2);
  ASSERT_EQ(consConstr1, consConstr1);
  ASSERT_FALSE(consConstr1 == consConstr2);
  ASSERT_EQ(head1, head1);
  ASSERT_FALSE(head1 == head2);
  ASSERT_EQ(dt1, dt1);
  ASSERT_FALSE(dt1 == dt2);

  ASSERT_EQ(std::hash<DatatypeDecl>{}(decl1), std::hash<DatatypeDecl>{}(decl1));
  ASSERT_EQ(std::hash<DatatypeDecl>{}(decl1), std::hash<DatatypeDecl>{}(decl2));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(cons1),
            std::hash<DatatypeConstructorDecl>{}(cons1));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(cons1),
            std::hash<DatatypeConstructorDecl>{}(cons2));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(nil1),
            std::hash<DatatypeConstructorDecl>{}(nil1));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(nil1),
            std::hash<DatatypeConstructorDecl>{}(nil2));
  ASSERT_EQ(std::hash<DatatypeConstructor>{}(consConstr1),
            std::hash<DatatypeConstructor>{}(consConstr1));
  ASSERT_EQ(std::hash<DatatypeConstructor>{}(consConstr1),
            std::hash<DatatypeConstructor>{}(consConstr2));
  ASSERT_EQ(std::hash<DatatypeSelector>{}(head1),
            std::hash<DatatypeSelector>{}(head1));
  ASSERT_EQ(std::hash<DatatypeSelector>{}(head1),
            std::hash<DatatypeSelector>{}(head2));
  ASSERT_EQ(std::hash<Datatype>{}(dt1), std::hash<Datatype>{}(dt1));
  ASSERT_EQ(std::hash<Datatype>{}(dt1), std::hash<Datatype>{}(dt2));

  (void)std::hash<DatatypeDecl>{}(DatatypeDecl());
  (void)std::hash<DatatypeConstructorDecl>{}(DatatypeConstructorDecl());
  (void)std::hash<DatatypeConstructor>{}(DatatypeConstructor());
  (void)std::hash<DatatypeSelector>{}(DatatypeSelector());
  (void)std::hash<Datatype>{}(Datatype());
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
  Sort unresTree = d_tm.mkUnresolvedDatatypeSort("tree");
  Sort unresList = d_tm.mkUnresolvedDatatypeSort("list");

  DatatypeDecl tree = d_tm.mkDatatypeDecl("tree");
  DatatypeConstructorDecl node = d_tm.mkDatatypeConstructorDecl("node");
  node.addSelector("left", unresTree);
  node.addSelector("right", unresTree);
  tree.addConstructor(node);

  DatatypeConstructorDecl leaf = d_tm.mkDatatypeConstructorDecl("leaf");
  leaf.addSelector("data", unresList);
  tree.addConstructor(leaf);

  DatatypeDecl list = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("car", unresTree);
  cons.addSelector("cdr", unresTree);
  list.addConstructor(cons);

  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  list.addConstructor(nil);

  std::vector<DatatypeDecl> dtdecls{tree, list};
  std::vector<Sort> dtsorts;
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
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
  std::vector<DatatypeDecl> dtdeclsBad{d_tm.mkDatatypeDecl("emptyD")};
  ASSERT_THROW(d_tm.mkDatatypeSorts(dtdeclsBad), CVC5ApiException);
}

TEST_F(TestApiBlackDatatype, mkDatatypeSortsSelUnres)
{
  // Same as above, without unresolved sorts

  DatatypeDecl tree = d_tm.mkDatatypeDecl("tree");
  DatatypeConstructorDecl node = d_tm.mkDatatypeConstructorDecl("node");
  node.addSelectorUnresolved("left", "tree");
  node.addSelectorUnresolved("right", "tree");
  tree.addConstructor(node);

  DatatypeConstructorDecl leaf = d_tm.mkDatatypeConstructorDecl("leaf");
  leaf.addSelectorUnresolved("data", "list");
  tree.addConstructor(leaf);

  DatatypeDecl list = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelectorUnresolved("car", "tree");
  cons.addSelectorUnresolved("cdr", "tree");
  list.addConstructor(cons);

  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  list.addConstructor(nil);

  std::vector<DatatypeDecl> dtdecls{tree, list};
  std::vector<Sort> dtsorts = d_tm.mkDatatypeSorts(dtdecls);
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
  Sort intSort = d_tm.getIntegerSort();
  Sort boolSort = d_tm.getBooleanSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", intSort);
  cons.addSelectorSelf("tail");
  Sort nullSort;
  ASSERT_THROW(cons.addSelector("null", nullSort), CVC5ApiException);
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_tm.mkDatatypeSort(dtypeSpec);
  Datatype dt = dtypeSort.getDatatype();
  ASSERT_FALSE(dt.isCodatatype());
  ASSERT_FALSE(dt.isTuple());
  ASSERT_FALSE(dt.isRecord());
  ASSERT_FALSE(dt.isFinite());
  ASSERT_TRUE(dt.isWellFounded());
  // get constructor
  DatatypeConstructor dcons = dt[0];
  (void)dcons.getTerm();
  ASSERT_EQ(dcons.getNumSelectors(), 2);

  // create datatype sort to test
  DatatypeDecl dtypeSpecEnum = d_tm.mkDatatypeDecl("enum");
  DatatypeConstructorDecl ca = d_tm.mkDatatypeConstructorDecl("A");
  dtypeSpecEnum.addConstructor(ca);
  DatatypeConstructorDecl cb = d_tm.mkDatatypeConstructorDecl("B");
  dtypeSpecEnum.addConstructor(cb);
  DatatypeConstructorDecl cc = d_tm.mkDatatypeConstructorDecl("C");
  dtypeSpecEnum.addConstructor(cc);
  Sort dtypeSortEnum = d_tm.mkDatatypeSort(dtypeSpecEnum);
  Datatype dtEnum = dtypeSortEnum.getDatatype();
  ASSERT_FALSE(dtEnum.isTuple());
  ASSERT_TRUE(dtEnum.isFinite());

  // create codatatype
  DatatypeDecl dtypeSpecStream = d_tm.mkDatatypeDecl("stream", true);
  DatatypeConstructorDecl consStream = d_tm.mkDatatypeConstructorDecl("cons");
  consStream.addSelector("head", intSort);
  consStream.addSelectorSelf("tail");
  dtypeSpecStream.addConstructor(consStream);
  Sort dtypeSortStream = d_tm.mkDatatypeSort(dtypeSpecStream);
  Datatype dtStream = dtypeSortStream.getDatatype();
  ASSERT_TRUE(dtStream.isCodatatype());
  ASSERT_FALSE(dtStream.isFinite());
  // codatatypes may be well-founded
  ASSERT_TRUE(dtStream.isWellFounded());

  // create tuple
  Sort tupSort = d_tm.mkTupleSort({boolSort});
  Datatype dtTuple = tupSort.getDatatype();
  ASSERT_TRUE(dtTuple.isTuple());
  ASSERT_FALSE(dtTuple.isRecord());
  ASSERT_TRUE(dtTuple.isFinite());
  ASSERT_TRUE(dtTuple.isWellFounded());

  // create record
  std::vector<std::pair<std::string, Sort>> fields = {
      std::make_pair("b", boolSort), std::make_pair("i", intSort)};
  Sort recSort = d_tm.mkRecordSort(fields);
  ASSERT_TRUE(recSort.isDatatype());
  Datatype dtRecord = recSort.getDatatype();
  ASSERT_FALSE(dtRecord.isTuple());
  ASSERT_TRUE(dtRecord.isRecord());
  ASSERT_FALSE(dtRecord.isFinite());
  ASSERT_TRUE(dtRecord.isWellFounded());
}

TEST_F(TestApiBlackDatatype, datatypeNames)
{
  Sort intSort = d_tm.getIntegerSort();

  // create datatype sort to test
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  ASSERT_NO_THROW(dtypeSpec.getName());
  ASSERT_EQ(dtypeSpec.getName(), std::string("list"));
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", intSort);
  cons.addSelectorSelf("tail");
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort dtypeSort = d_tm.mkDatatypeSort(dtypeSpec);
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
  Sort t1 = d_tm.mkParamSort("T1");
  Sort t2 = d_tm.mkParamSort("T2");
  std::vector<Sort> v{t1, t2};
  DatatypeDecl pairSpec = d_tm.mkDatatypeDecl("pair", v);

  DatatypeConstructorDecl mkpair = d_tm.mkDatatypeConstructorDecl("mk-pair");
  mkpair.addSelector("first", t1);
  mkpair.addSelector("second", t2);
  pairSpec.addConstructor(mkpair);

  Sort pairSort = d_tm.mkDatatypeSort(pairSpec);

  ASSERT_TRUE(pairSort.getDatatype().isParametric());
  std::vector<Sort> dparams = pairSort.getDatatype().getParameters();
  ASSERT_TRUE(dparams[0] == t1 && dparams[1] == t2);

  v.clear();
  v.push_back(d_tm.getIntegerSort());
  v.push_back(d_tm.getIntegerSort());
  Sort pairIntInt = pairSort.instantiate(v);
  v.clear();
  v.push_back(d_tm.getRealSort());
  v.push_back(d_tm.getRealSort());
  Sort pairRealReal = pairSort.instantiate(v);
  v.clear();
  v.push_back(d_tm.getRealSort());
  v.push_back(d_tm.getIntegerSort());
  Sort pairRealInt = pairSort.instantiate(v);
  v.clear();
  v.push_back(d_tm.getIntegerSort());
  v.push_back(d_tm.getRealSort());
  Sort pairIntReal = pairSort.instantiate(v);

  ASSERT_NE(pairIntInt, pairRealReal);
  ASSERT_NE(pairIntReal, pairRealReal);
  ASSERT_NE(pairRealInt, pairRealReal);
  ASSERT_NE(pairIntInt, pairIntReal);
  ASSERT_NE(pairIntInt, pairRealInt);
  ASSERT_NE(pairIntReal, pairRealInt);
}

TEST_F(TestApiBlackDatatype, isFinite)
{
  DatatypeDecl dtypedecl = d_tm.mkDatatypeDecl("dt", {});
  DatatypeConstructorDecl ctordecl = d_tm.mkDatatypeConstructorDecl("cons");
  ctordecl.addSelector("sel", d_tm.getBooleanSort());
  dtypedecl.addConstructor(ctordecl);
  Sort dtype = d_tm.mkDatatypeSort(dtypedecl);
  ASSERT_TRUE(dtype.getDatatype().isFinite());

  Sort p = d_tm.mkParamSort("p1");
  DatatypeDecl pdtypedecl = d_tm.mkDatatypeDecl("dt", {p});
  DatatypeConstructorDecl pctordecl = d_tm.mkDatatypeConstructorDecl("cons");
  pctordecl.addSelector("sel", p);
  pdtypedecl.addConstructor(pctordecl);
  Sort pdtype = d_tm.mkDatatypeSort(pdtypedecl);
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
  Sort unresWList = d_tm.mkUnresolvedDatatypeSort("wlist");
  Sort unresList = d_tm.mkUnresolvedDatatypeSort("list");

  DatatypeDecl wlist = d_tm.mkDatatypeDecl("wlist");
  DatatypeConstructorDecl leaf = d_tm.mkDatatypeConstructorDecl("leaf");
  leaf.addSelector("data", unresList);
  wlist.addConstructor(leaf);

  DatatypeDecl list = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("car", unresWList);
  cons.addSelector("cdr", unresList);
  list.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  list.addConstructor(nil);

  DatatypeDecl ns = d_tm.mkDatatypeDecl("ns");
  DatatypeConstructorDecl elem = d_tm.mkDatatypeConstructorDecl("elem");
  elem.addSelector("ndata", d_tm.mkSetSort(unresWList));
  ns.addConstructor(elem);
  DatatypeConstructorDecl elemArray =
      d_tm.mkDatatypeConstructorDecl("elemArray");
  elemArray.addSelector("ndata", d_tm.mkArraySort(unresList, unresList));
  ns.addConstructor(elemArray);

  std::vector<DatatypeDecl> dtdecls{wlist, list, ns};
  // this is well-founded and has no nested recursion
  std::vector<Sort> dtsorts;
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 3);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[1].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[2].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     ns2 = elem2(ndata: array(int,ns2)) | nil2
   *   END;
   */
  Sort unresNs2 = d_tm.mkUnresolvedDatatypeSort("ns2");

  DatatypeDecl ns2 = d_tm.mkDatatypeDecl("ns2");
  DatatypeConstructorDecl elem2 = d_tm.mkDatatypeConstructorDecl("elem2");
  elem2.addSelector("ndata", d_tm.mkArraySort(d_tm.getIntegerSort(), unresNs2));
  ns2.addConstructor(elem2);
  DatatypeConstructorDecl nil2 = d_tm.mkDatatypeConstructorDecl("nil2");
  ns2.addConstructor(nil2);

  dtdecls = {ns2};
  // this is not well-founded due to non-simple recursion
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
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
  Sort unresNs3 = d_tm.mkUnresolvedDatatypeSort("ns3");
  Sort unresList3 = d_tm.mkUnresolvedDatatypeSort("list3");

  DatatypeDecl list3 = d_tm.mkDatatypeDecl("list3");
  DatatypeConstructorDecl cons3 = d_tm.mkDatatypeConstructorDecl("cons3");
  cons3.addSelector("car", unresNs3);
  cons3.addSelector("cdr", unresList3);
  list3.addConstructor(cons3);
  DatatypeConstructorDecl nil3 = d_tm.mkDatatypeConstructorDecl("nil3");
  list3.addConstructor(nil3);

  DatatypeDecl ns3 = d_tm.mkDatatypeDecl("ns3");
  DatatypeConstructorDecl elem3 = d_tm.mkDatatypeConstructorDecl("elem3");
  elem3.addSelector("ndata", d_tm.mkSetSort(unresList3));
  ns3.addConstructor(elem3);

  dtdecls = {list3, ns3};

  // both are well-founded and have nested recursion
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 2);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[1].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list4 = cons(car: set(ns4), cdr: list4) | nil,
   *     ns4 = elem(ndata: list4)
   *   END;
   */
  Sort unresNs4 = d_tm.mkUnresolvedDatatypeSort("ns4");
  Sort unresList4 = d_tm.mkUnresolvedDatatypeSort("list4");

  DatatypeDecl list4 = d_tm.mkDatatypeDecl("list4");
  DatatypeConstructorDecl cons4 = d_tm.mkDatatypeConstructorDecl("cons4");
  cons4.addSelector("car", d_tm.mkSetSort(unresNs4));
  cons4.addSelector("cdr", unresList4);
  list4.addConstructor(cons4);
  DatatypeConstructorDecl nil4 = d_tm.mkDatatypeConstructorDecl("nil4");
  list4.addConstructor(nil4);

  DatatypeDecl ns4 = d_tm.mkDatatypeDecl("ns4");
  DatatypeConstructorDecl elem4 = d_tm.mkDatatypeConstructorDecl("elem3");
  elem4.addSelector("ndata", unresList4);
  ns4.addConstructor(elem4);

  dtdecls = {list4, ns4};
  // both are well-founded and have nested recursion
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 2);
  ASSERT_TRUE(dtsorts[0].getDatatype().isWellFounded());
  ASSERT_TRUE(dtsorts[1].getDatatype().isWellFounded());

  /* Create mutual datatypes corresponding to this definition block:
   *   DATATYPE
   *     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
   *   END;
   */
  Sort unresList5 = d_tm.mkUninterpretedSortConstructorSort(1, "list5");

  Sort x = d_tm.mkParamSort("X");
  std::vector<Sort> v{x};

  DatatypeDecl list5 = d_tm.mkDatatypeDecl("list5", v);
  std::vector<Sort> args{x};
  Sort urListX = unresList5.instantiate(args);
  args[0] = urListX;
  Sort urListListX = unresList5.instantiate(args);

  DatatypeConstructorDecl cons5 = d_tm.mkDatatypeConstructorDecl("cons5");
  cons5.addSelector("car", x);
  cons5.addSelector("cdr", urListListX);
  list5.addConstructor(cons5);
  DatatypeConstructorDecl nil5 = d_tm.mkDatatypeConstructorDecl("nil5");
  list5.addConstructor(nil5);

  dtdecls = {list5};
  // well-founded and has nested recursion
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
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
  Sort unresList = d_tm.mkUninterpretedSortConstructorSort(1, "plist");

  Sort x = d_tm.mkParamSort("X");
  std::vector<Sort> v{x};
  DatatypeDecl plist = d_tm.mkDatatypeDecl("plist", v);

  std::vector<Sort> args{x};
  Sort urListX = unresList.instantiate(args);

  DatatypeConstructorDecl pcons = d_tm.mkDatatypeConstructorDecl("pcons");
  pcons.addSelector("car", x);
  pcons.addSelector("cdr", urListX);
  plist.addConstructor(pcons);
  DatatypeConstructorDecl nil5 = d_tm.mkDatatypeConstructorDecl("pnil");
  plist.addConstructor(nil5);

  std::vector<DatatypeDecl> dtdecls{plist};

  std::vector<Sort> dtsorts;
  // make the datatype sorts
  ASSERT_NO_THROW(dtsorts = d_tm.mkDatatypeSorts(dtdecls));
  ASSERT_EQ(dtsorts.size(), 1);
  Datatype d = dtsorts[0].getDatatype();
  DatatypeConstructor nilc = d[0];

  Sort isort = d_tm.getIntegerSort();
  std::vector<Sort> iargs{isort};
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
