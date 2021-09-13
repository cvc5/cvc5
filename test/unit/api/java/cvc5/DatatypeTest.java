/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the datatype classes of the Java API.
 */

package cvc5;

import static cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class DatatypeTest
{
  private Solver d_solver;

  @BeforeEach void setUp()
  {
    d_solver = new Solver();
  }

  @Test void mkDatatypeSort() throws CVC5ApiException
  {
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort listSort = d_solver.mkDatatypeSort(dtypeSpec);
    Datatype d = listSort.getDatatype();
    DatatypeConstructor consConstr = d.getConstructor(0);
    DatatypeConstructor nilConstr = d.getConstructor(1);
    assertThrows(CVC5ApiException.class, () -> d.getConstructor(2));
    assertDoesNotThrow(() -> consConstr.getConstructorTerm());
    assertDoesNotThrow(() -> nilConstr.getConstructorTerm());
  }

  @Test void mkDatatypeSorts()
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
    Set<Sort> unresTypes = new HashSet<>();
    Sort unresTree = d_solver.mkUninterpretedSort("tree");
    Sort unresList = d_solver.mkUninterpretedSort("list");
    unresTypes.add(unresTree);
    unresTypes.add(unresList);

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

    List<DatatypeDecl> dtdecls = new ArrayList<>();
    dtdecls.add(tree);
    dtdecls.add(list);

    AtomicReference<List<Sort>> atomic = new AtomicReference<>();
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    List<Sort> dtsorts = atomic.get();
    assertEquals(dtsorts.size(), dtdecls.size());
    for (int i = 0, ndecl = dtdecls.size(); i < ndecl; i++)
    {
      assertTrue(dtsorts.get(i).isDatatype());
      assertFalse(dtsorts.get(i).getDatatype().isFinite());
      assertEquals(dtsorts.get(i).getDatatype().getName(), dtdecls.get(i).getName());
    }
    // verify the resolution was correct
    Datatype dtTree = dtsorts.get(0).getDatatype();
    DatatypeConstructor dtcTreeNode = dtTree.getConstructor(0);
    assertEquals(dtcTreeNode.getName(), "node");
    DatatypeSelector dtsTreeNodeLeft = dtcTreeNode.getSelector(0);
    assertEquals(dtsTreeNodeLeft.getName(), "left");
    // argument type should have resolved to be recursive
    assertTrue(dtsTreeNodeLeft.getRangeSort().isDatatype());
    assertEquals(dtsTreeNodeLeft.getRangeSort(), dtsorts.get(0));

    // fails due to empty datatype
    List<DatatypeDecl> dtdeclsBad = new ArrayList<>();
    DatatypeDecl emptyD = d_solver.mkDatatypeDecl("emptyD");
    dtdeclsBad.add(emptyD);
    assertThrows(CVC5ApiException.class, () -> d_solver.mkDatatypeSorts(dtdeclsBad));
  }

  @Test void datatypeStructs() throws CVC5ApiException
  {
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();

    // create datatype sort to test
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", intSort);
    cons.addSelectorSelf("tail");
    Sort nullSort = d_solver.getNullSort();
    assertThrows(CVC5ApiException.class, () -> cons.addSelector("null", nullSort));
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
    Datatype dt = dtypeSort.getDatatype();
    assertFalse(dt.isCodatatype());
    assertFalse(dt.isTuple());
    assertFalse(dt.isRecord());
    assertFalse(dt.isFinite());
    assertTrue(dt.isWellFounded());
    // get constructor
    DatatypeConstructor dcons = dt.getConstructor(0);
    Term consTerm = dcons.getConstructorTerm();
    assertEquals(dcons.getNumSelectors(), 2);

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
    assertFalse(dtEnum.isTuple());
    assertTrue(dtEnum.isFinite());

    // create codatatype
    DatatypeDecl dtypeSpecStream = d_solver.mkDatatypeDecl("stream", true);
    DatatypeConstructorDecl consStream = d_solver.mkDatatypeConstructorDecl("cons");
    consStream.addSelector("head", intSort);
    consStream.addSelectorSelf("tail");
    dtypeSpecStream.addConstructor(consStream);
    Sort dtypeSortStream = d_solver.mkDatatypeSort(dtypeSpecStream);
    Datatype dtStream = dtypeSortStream.getDatatype();
    assertTrue(dtStream.isCodatatype());
    assertFalse(dtStream.isFinite());
    // codatatypes may be well-founded
    assertTrue(dtStream.isWellFounded());

    // create tuple
    Sort tupSort = d_solver.mkTupleSort(new Sort[] {boolSort});
    Datatype dtTuple = tupSort.getDatatype();
    assertTrue(dtTuple.isTuple());
    assertFalse(dtTuple.isRecord());
    assertTrue(dtTuple.isFinite());
    assertTrue(dtTuple.isWellFounded());

    // create record
    Pair<String, Sort>[] fields = new Pair[] {new Pair<>("b", boolSort), new Pair<>("i", intSort)};
    Sort recSort = d_solver.mkRecordSort(fields);
    assertTrue(recSort.isDatatype());
    Datatype dtRecord = recSort.getDatatype();
    assertFalse(dtRecord.isTuple());
    assertTrue(dtRecord.isRecord());
    assertFalse(dtRecord.isFinite());
    assertTrue(dtRecord.isWellFounded());
  }

  @Test void datatypeNames() throws CVC5ApiException
  {
    Sort intSort = d_solver.getIntegerSort();

    // create datatype sort to test
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    assertDoesNotThrow(() -> dtypeSpec.getName());
    assertEquals(dtypeSpec.getName(), "list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", intSort);
    cons.addSelectorSelf("tail");
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
    Datatype dt = dtypeSort.getDatatype();
    assertEquals(dt.getName(), "list");
    assertDoesNotThrow(() -> dt.getConstructor("nil"));
    assertDoesNotThrow(() -> dt.getConstructor("cons"));
    assertThrows(CVC5ApiException.class, () -> dt.getConstructor("head"));
    assertThrows(CVC5ApiException.class, () -> dt.getConstructor(""));

    DatatypeConstructor dcons = dt.getConstructor(0);
    assertEquals(dcons.getName(), "cons");
    assertDoesNotThrow(() -> dcons.getSelector("head"));
    assertDoesNotThrow(() -> dcons.getSelector("tail"));
    assertThrows(CVC5ApiException.class, () -> dcons.getSelector("cons"));

    // get selector
    DatatypeSelector dselTail = dcons.getSelector(1);
    assertEquals(dselTail.getName(), "tail");
    assertEquals(dselTail.getRangeSort(), dtypeSort);

    // possible to construct null datatype declarations if not using solver
    assertThrows(CVC5ApiException.class, () -> d_solver.getNullDatatypeDecl().getName());
  }

  @Test void parametricDatatype() throws CVC5ApiException
  {
    List<Sort> v = new ArrayList<>();
    Sort t1 = d_solver.mkParamSort("T1");
    Sort t2 = d_solver.mkParamSort("T2");
    v.add(t1);
    v.add(t2);
    DatatypeDecl pairSpec = d_solver.mkDatatypeDecl("pair", v);

    DatatypeConstructorDecl mkpair = d_solver.mkDatatypeConstructorDecl("mk-pair");
    mkpair.addSelector("first", t1);
    mkpair.addSelector("second", t2);
    pairSpec.addConstructor(mkpair);

    Sort pairType = d_solver.mkDatatypeSort(pairSpec);

    assertTrue(pairType.getDatatype().isParametric());

    v.clear();
    v.add(d_solver.getIntegerSort());
    v.add(d_solver.getIntegerSort());
    Sort pairIntInt = pairType.instantiate(v);
    v.clear();
    v.add(d_solver.getRealSort());
    v.add(d_solver.getRealSort());
    Sort pairRealReal = pairType.instantiate(v);
    v.clear();
    v.add(d_solver.getRealSort());
    v.add(d_solver.getIntegerSort());
    Sort pairRealInt = pairType.instantiate(v);
    v.clear();
    v.add(d_solver.getIntegerSort());
    v.add(d_solver.getRealSort());
    Sort pairIntReal = pairType.instantiate(v);

    assertNotEquals(pairIntInt, pairRealReal);
    assertNotEquals(pairIntReal, pairRealReal);
    assertNotEquals(pairRealInt, pairRealReal);
    assertNotEquals(pairIntInt, pairIntReal);
    assertNotEquals(pairIntInt, pairRealInt);
    assertNotEquals(pairIntReal, pairRealInt);

    assertTrue(pairRealReal.isComparableTo(pairRealReal));
    assertFalse(pairIntReal.isComparableTo(pairRealReal));
    assertFalse(pairRealInt.isComparableTo(pairRealReal));
    assertFalse(pairIntInt.isComparableTo(pairRealReal));
    assertFalse(pairRealReal.isComparableTo(pairRealInt));
    assertFalse(pairIntReal.isComparableTo(pairRealInt));
    assertTrue(pairRealInt.isComparableTo(pairRealInt));
    assertFalse(pairIntInt.isComparableTo(pairRealInt));
    assertFalse(pairRealReal.isComparableTo(pairIntReal));
    assertTrue(pairIntReal.isComparableTo(pairIntReal));
    assertFalse(pairRealInt.isComparableTo(pairIntReal));
    assertFalse(pairIntInt.isComparableTo(pairIntReal));
    assertFalse(pairRealReal.isComparableTo(pairIntInt));
    assertFalse(pairIntReal.isComparableTo(pairIntInt));
    assertFalse(pairRealInt.isComparableTo(pairIntInt));
    assertTrue(pairIntInt.isComparableTo(pairIntInt));

    assertTrue(pairRealReal.isSubsortOf(pairRealReal));
    assertFalse(pairIntReal.isSubsortOf(pairRealReal));
    assertFalse(pairRealInt.isSubsortOf(pairRealReal));
    assertFalse(pairIntInt.isSubsortOf(pairRealReal));
    assertFalse(pairRealReal.isSubsortOf(pairRealInt));
    assertFalse(pairIntReal.isSubsortOf(pairRealInt));
    assertTrue(pairRealInt.isSubsortOf(pairRealInt));
    assertFalse(pairIntInt.isSubsortOf(pairRealInt));
    assertFalse(pairRealReal.isSubsortOf(pairIntReal));
    assertTrue(pairIntReal.isSubsortOf(pairIntReal));
    assertFalse(pairRealInt.isSubsortOf(pairIntReal));
    assertFalse(pairIntInt.isSubsortOf(pairIntReal));
    assertFalse(pairRealReal.isSubsortOf(pairIntInt));
    assertFalse(pairIntReal.isSubsortOf(pairIntInt));
    assertFalse(pairRealInt.isSubsortOf(pairIntInt));
    assertTrue(pairIntInt.isSubsortOf(pairIntInt));
  }

  @Test void datatypeSimplyRec() throws CVC5ApiException
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
    Set<Sort> unresTypes = new HashSet<>();
    Sort unresWList = d_solver.mkUninterpretedSort("wlist");
    Sort unresList = d_solver.mkUninterpretedSort("list");
    Sort unresNs = d_solver.mkUninterpretedSort("ns");
    unresTypes.add(unresWList);
    unresTypes.add(unresList);
    unresTypes.add(unresNs);

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
    DatatypeConstructorDecl elemArray = d_solver.mkDatatypeConstructorDecl("elemArray");
    elemArray.addSelector("ndata", d_solver.mkArraySort(unresList, unresList));
    ns.addConstructor(elemArray);

    List<DatatypeDecl> dtdecls = new ArrayList<>();
    dtdecls.add(wlist);
    dtdecls.add(list);
    dtdecls.add(ns);
    // this is well-founded and has no nested recursion
    AtomicReference<List<Sort>> atomic = new AtomicReference<>();
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    List<Sort> dtsorts = atomic.get();
    assertEquals(dtsorts.size(), 3);
    assertTrue(dtsorts.get(0).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(1).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(2).getDatatype().isWellFounded());
    assertFalse(dtsorts.get(0).getDatatype().hasNestedRecursion());
    assertFalse(dtsorts.get(1).getDatatype().hasNestedRecursion());
    assertFalse(dtsorts.get(2).getDatatype().hasNestedRecursion());

    /* Create mutual datatypes corresponding to this definition block:
     *   DATATYPE
     *     ns2 = elem2(ndata: array(int,ns2)) | nil2
     *   END;
     */
    unresTypes.clear();
    Sort unresNs2 = d_solver.mkUninterpretedSort("ns2");
    unresTypes.add(unresNs2);

    DatatypeDecl ns2 = d_solver.mkDatatypeDecl("ns2");
    DatatypeConstructorDecl elem2 = d_solver.mkDatatypeConstructorDecl("elem2");
    elem2.addSelector("ndata", d_solver.mkArraySort(d_solver.getIntegerSort(), unresNs2));
    ns2.addConstructor(elem2);
    DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil2");
    ns2.addConstructor(nil2);

    dtdecls.clear();
    dtdecls.add(ns2);

    // dtsorts.clear();
    // this is not well-founded due to non-simple recursion
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    dtsorts = atomic.get();
    assertEquals(dtsorts.size(), 1);
    assertTrue(
        dtsorts.get(0).getDatatype().getConstructor(0).getSelector(0).getRangeSort().isArray());
    assertEquals(dtsorts.get(0)
                     .getDatatype()
                     .getConstructor(0)
                     .getSelector(0)
                     .getRangeSort()
                     .getArrayElementSort(),
        dtsorts.get(0));
    assertTrue(dtsorts.get(0).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(0).getDatatype().hasNestedRecursion());

    /* Create mutual datatypes corresponding to this definition block:
     *   DATATYPE
     *     list3 = cons3(car: ns3, cdr: list3) | nil3,
     *     ns3 = elem3(ndata: set(list3))
     *   END;
     */
    unresTypes.clear();
    Sort unresNs3 = d_solver.mkUninterpretedSort("ns3");
    unresTypes.add(unresNs3);
    Sort unresList3 = d_solver.mkUninterpretedSort("list3");
    unresTypes.add(unresList3);

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
    dtdecls.add(list3);
    dtdecls.add(ns3);

    // dtsorts.clear();
    // both are well-founded and have nested recursion
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    dtsorts = atomic.get();
    assertEquals(dtsorts.size(), 2);
    assertTrue(dtsorts.get(0).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(1).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(0).getDatatype().hasNestedRecursion());
    assertTrue(dtsorts.get(1).getDatatype().hasNestedRecursion());

    /* Create mutual datatypes corresponding to this definition block:
     *   DATATYPE
     *     list4 = cons(car: set(ns4), cdr: list4) | nil,
     *     ns4 = elem(ndata: list4)
     *   END;
     */
    unresTypes.clear();
    Sort unresNs4 = d_solver.mkUninterpretedSort("ns4");
    unresTypes.add(unresNs4);
    Sort unresList4 = d_solver.mkUninterpretedSort("list4");
    unresTypes.add(unresList4);

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
    dtdecls.add(list4);
    dtdecls.add(ns4);

    // dtsorts.clear();
    // both are well-founded and have nested recursion
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    dtsorts = atomic.get();
    assertEquals(dtsorts.size(), 2);
    assertTrue(dtsorts.get(0).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(1).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(0).getDatatype().hasNestedRecursion());
    assertTrue(dtsorts.get(1).getDatatype().hasNestedRecursion());

    /* Create mutual datatypes corresponding to this definition block:
     *   DATATYPE
     *     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
     *   END;
     */
    unresTypes.clear();
    Sort unresList5 = d_solver.mkSortConstructorSort("list5", 1);
    unresTypes.add(unresList5);

    List<Sort> v = new ArrayList<>();
    Sort x = d_solver.mkParamSort("X");
    v.add(x);
    DatatypeDecl list5 = d_solver.mkDatatypeDecl("list5", v);

    List<Sort> args = new ArrayList<>();
    args.add(x);
    Sort urListX = unresList5.instantiate(args);
    args.set(0, urListX);
    Sort urListListX = unresList5.instantiate(args);

    DatatypeConstructorDecl cons5 = d_solver.mkDatatypeConstructorDecl("cons5");
    cons5.addSelector("car", x);
    cons5.addSelector("cdr", urListListX);
    list5.addConstructor(cons5);
    DatatypeConstructorDecl nil5 = d_solver.mkDatatypeConstructorDecl("nil5");
    list5.addConstructor(nil5);

    dtdecls.clear();
    dtdecls.add(list5);

    // well-founded and has nested recursion
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    dtsorts = atomic.get();
    assertEquals(dtsorts.size(), 1);
    assertTrue(dtsorts.get(0).getDatatype().isWellFounded());
    assertTrue(dtsorts.get(0).getDatatype().hasNestedRecursion());
  }

  @Test void datatypeSpecializedCons() throws CVC5ApiException
  {
    /* Create mutual datatypes corresponding to this definition block:
     *   DATATYPE
     *     plist[X] = pcons(car: X, cdr: plist[X]) | pnil
     *   END;
     */
    // Make unresolved types as placeholders
    Set<Sort> unresTypes = new HashSet<>();
    Sort unresList = d_solver.mkSortConstructorSort("plist", 1);
    unresTypes.add(unresList);

    List<Sort> v = new ArrayList<>();
    Sort x = d_solver.mkParamSort("X");
    v.add(x);
    DatatypeDecl plist = d_solver.mkDatatypeDecl("plist", v);

    List<Sort> args = new ArrayList<>();
    args.add(x);
    Sort urListX = unresList.instantiate(args);

    DatatypeConstructorDecl pcons = d_solver.mkDatatypeConstructorDecl("pcons");
    pcons.addSelector("car", x);
    pcons.addSelector("cdr", urListX);
    plist.addConstructor(pcons);
    DatatypeConstructorDecl nil5 = d_solver.mkDatatypeConstructorDecl("pnil");
    plist.addConstructor(nil5);

    List<DatatypeDecl> dtdecls = new ArrayList<>();
    dtdecls.add(plist);

    // make the datatype sorts
    AtomicReference<List<Sort>> atomic = new AtomicReference<>();
    assertDoesNotThrow(() -> atomic.set(d_solver.mkDatatypeSorts(dtdecls, unresTypes)));
    List<Sort> dtsorts = atomic.get();
    assertEquals(dtsorts.size(), 1);
    Datatype d = dtsorts.get(0).getDatatype();
    DatatypeConstructor nilc = d.getConstructor(0);

    Sort isort = d_solver.getIntegerSort();
    List<Sort> iargs = new ArrayList<>();
    iargs.add(isort);
    Sort listInt = dtsorts.get(0).instantiate(iargs);

    AtomicReference<Term> atomicTerm = new AtomicReference<>();
    // get the specialized constructor term for list[Int]
    assertDoesNotThrow(() -> atomicTerm.set(nilc.getSpecializedConstructorTerm(listInt)));
    Term testConsTerm = atomicTerm.get();
    assertNotEquals(testConsTerm, nilc.getConstructorTerm());
    // error to get the specialized constructor term for Int
    assertThrows(CVC5ApiException.class, () -> nilc.getSpecializedConstructorTerm(isort));
  }
}
