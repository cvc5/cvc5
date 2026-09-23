/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for the theory of bags.
 */

#include "theory/bags/bag_solver.h"

#include "expr/bound_var_manager.h"
#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "options/bags_options.h"
#include "theory/bags/bags_utils.h"
#include "theory/bags/inference_generator.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

BagSolver::BagSolver(Env& env, SolverState& s, InferenceManager& im)
    : EnvObj(env),
      d_state(s),
      d_ig(env.getNodeManager(), &s, &im, options().bags.bagsToLiastar),
      d_im(im),
      d_mapCache(userContext())
{
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

BagSolver::~BagSolver() {}

void BagSolver::checkBasicOperations()
{
  checkDisequalBagTerms();

  // At this point, all bag and count representatives should be in the solver
  // state.
  for (const Node& bag : d_state.getBags())
  {
    // iterate through all bags terms in each equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case Kind::BAG_EMPTY: checkEmpty(n); break;
        case Kind::BAG_MAKE: checkBagMake(n); break;
        case Kind::BAG_UNION_DISJOINT: checkUnionDisjoint(n); break;
        case Kind::BAG_UNION_MAX: checkUnionMax(n); break;
        case Kind::BAG_INTER_MIN: checkIntersectionMin(n); break;
        case Kind::BAG_DIFFERENCE_SUBTRACT: checkDifferenceSubtract(n); break;
        case Kind::BAG_DIFFERENCE_REMOVE: checkDifferenceRemove(n); break;
        case Kind::BAG_SETOF: checkSetof(n); break;
        case Kind::BAG_FILTER: checkFilter(n); break;
        case Kind::TABLE_PRODUCT: checkProduct(n); break;
        case Kind::TABLE_JOIN: checkJoin(n); break;
        case Kind::TABLE_GROUP: checkGroup(n); break;
        default: break;
      }
      it++;
    }
  }

  // add non negative constraints for all multiplicities
  for (const Node& n : d_state.getBags())
  {
    for (const Node& e : d_state.getElements(n))
    {
      checkNonNegativeCountTerms(n, d_state.getRepresentative(e));
    }
  }
}

void BagSolver::checkLiastarConstraints()
{
  if (!options().bags.bagsToLiastar)
  {
    return;
  }
  // Both maps are state of this check, not caches. The keys of d_bagBoundVars
  // are the bags the star ranges over, and they must be the bags of the
  // current context: these maps are plain maps, so they would never shrink on
  // backtracking, and every later star would carry the bags of the branches
  // that were abandoned in between. The values of d_cardinalityVars depend on
  // the context as well, since getCardinalityVar reuses the skolem that the
  // current context registered for (bag.card bag), and the cardinality terms
  // of the state are themselves collected afresh by TheoryBags::initialize,
  // under the representatives of the current context.
  d_cardinalityVars.clear();
  d_bagBoundVars.clear();

  eq::EqualityEngine* ee = d_state.getEqualityEngine();

  // The bag atoms are literals of the current context, so the positive top
  // level atoms are the equalities in the equivalence class of true, and the
  // non top level atoms of step 1 are the equalities in the equivalence class
  // of false.
  std::vector<Node> equalities;
  std::vector<Node> disequalities;
  eq::EqClassIterator trueIt = eq::EqClassIterator(d_true, ee);
  while (!trueIt.isFinished())
  {
    Node n = (*trueIt);
    if (n.getKind() == Kind::EQUAL && n[0].getType().isBag())
    {
      equalities.push_back(n);
    }
    ++trueIt;
  }
  eq::EqClassIterator falseIt = eq::EqClassIterator(d_false, ee);
  while (!falseIt.isFinished())
  {
    Node n = (*falseIt);
    if (n.getKind() == Kind::EQUAL && n[0].getType().isBag())
    {
      disequalities.push_back(n);
    }
    ++falseIt;
  }
  const std::map<Node, Node>& cardTerms = d_state.getCardinalityTerms();
  Trace("bags-liastar") << "equalities: " << equalities << std::endl;
  Trace("bags-liastar") << "disequalities: " << disequalities << std::endl;
  if (equalities.empty() && disequalities.empty() && cardTerms.empty())
  {
    // there is nothing to translate
    return;
  }

  // the bags of the positive atoms need slots in the star, and so do the bags
  // whose cardinality the input constrains, even when they occur in no atom:
  // the star is the only thing that relates a cardinality term to the bag it
  // is the cardinality of
  for (const Node& equality : equalities)
  {
    getBagBoundVar(equality[0]);
    getBagBoundVar(equality[1]);
  }
  for (const std::pair<const Node, Node>& pair : cardTerms)
  {
    Assert(pair.first.getKind() == Kind::BAG_CARD);
    getBagBoundVar(pair.first[0]);
  }
  // step 1: move the negated atoms out of the star. This introduces the
  // difference bags, which get their slots here so that step 3 below sees
  // them.
  for (const Node& disequality : disequalities)
  {
    evictNegatedAtom(disequality);
  }
  // step 3
  addCardinalityVars();
  // the constraints of the constructed bags, which Figure 4 does not cover
  addBagMakeCardinalities();
  // step 4
  std::vector<Node> premises;
  Node star = buildStar(equalities, premises);
  // Part of the body only holds in the contexts the conjuncts were read from,
  // and buildStar collected those contexts in premises. The star must be
  // guarded by them: a lemma is asserted at the assertion level, not at the
  // current decision level, so an unguarded star would keep forcing
  // (= c_A c_B) at every element in the branches where A and B are not equal,
  // which would refute satisfiable inputs. The negated atoms need no guard
  // here since they contribute nothing to the body; each of them is asserted
  // by its own guarded lemma in evictNegatedAtom above.
  Node lemma =
      premises.empty() ? star : nodeManager()->mkAnd(premises).impNode(star);
  Trace("bags-liastar") << "lemma: " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR);
}

void BagSolver::evictNegatedAtom(const Node& equality)
{
  Assert(equality.getKind() == Kind::EQUAL && equality[0].getType().isBag());
  NodeManager* nm = nodeManager();
  Node A = equality[0];
  Node B = equality[1];
  // the bound variables of A and B are related to those of the difference
  // bags by the pointwise definitions of the latter
  Node AminusB = rewrite(nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, A, B));
  Node BminusA = rewrite(nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, B, A));
  getBagBoundVar(A);
  getBagBoundVar(B);
  getBagBoundVar(AminusB);
  getBagBoundVar(BminusA);

  Node xA = getCardinalityVar(A);
  Node xB = getCardinalityVar(B);
  Node xAminusB = getCardinalityVar(AminusB);
  Node xBminusA = getCardinalityVar(BminusA);
  Node cards = nm->mkNode(
      Kind::AND,
      {xA.eqNode(xB), xAminusB.eqNode(d_zero), xBminusA.eqNode(d_zero)});
  // (or (= A B) (not (and (= x_A x_B) (= x_{A - B} 0) (= x_{B - A} 0))))
  // Note this lemma is valid, and not merely a consequence of the current
  // context: the cardinality variables are exactly the cardinalities of their
  // bags, and two bags are equal iff both their differences are empty.
  Node lemma = equality.orNode(cards.notNode());
  Trace("bags-liastar") << "evict " << equality << ": " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR);
}

void BagSolver::addCardinalityVars()
{
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    getCardinalityVar(pair.first);
  }
}

Node BagSolver::buildStar(const std::vector<Node>& equalities,
                          std::vector<Node>& premises)
{
  NodeManager* nm = nodeManager();
  // one fixed order for both vectors
  std::vector<Node> bags;
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    bags.push_back(pair.first);
  }
  // the outer vector, the inner vector, and the body of the star
  std::vector<Node> cardinalities;
  std::vector<Node> boundVars;
  std::vector<Node> constraints;
  for (const Node& bag : bags)
  {
    Node c = d_bagBoundVars[bag];
    Node x = getCardinalityVar(bag);
    boundVars.push_back(c);
    cardinalities.push_back(x);
    // the cardinality variables are skolems whose names do not mention their
    // bags, so print the slots of bag here
    Trace("bags-liastar") << "slot " << bag << ": cardinality = " << x
                          << ", bound var = " << c << std::endl;
    // a count is non negative. Never omit the sign constraints: negative
    // summands would let the star cancel, and a cardinality of zero would no
    // longer mean that the bag is empty.
    constraints.push_back(nm->mkNode(Kind::GEQ, c, d_zero));
    if (hasPointwiseTranslation(bag.getKind()))
    {
      constraints.push_back(getPointwiseConstraint(bag));
    }
    else if (bag.getKind() == Kind::BAG_MAKE)
    {
      addBagMakeConstraints(bag, constraints);
    }
  }
  // the positive atoms hold at every element
  for (const Node& equality : equalities)
  {
    constraints.push_back(
        d_bagBoundVars[equality[0]].eqNode(d_bagBoundVars[equality[1]]));
    premises.push_back(equality);
  }
  addBagMakeOverlaps(constraints, premises);
  // no bag term was discovered while building the body, so the two vectors
  // cover all the bound variables that occur in it
  Assert(d_bagBoundVars.size() == bags.size());

  Node boundVarList = nm->mkNode(Kind::BOUND_VAR_LIST, boundVars);
  Node lambda = nm->mkNode(Kind::LAMBDA, boundVarList, nm->mkAnd(constraints));
  std::vector<Node> children;
  children.push_back(lambda);
  children.insert(children.end(), cardinalities.begin(), cardinalities.end());
  return nm->mkNode(Kind::STAR_CONTAINS, children);
}

Node BagSolver::getCardinalityVar(const Node& bag)
{
  Assert(bag.getType().isBag());
  std::map<Node, Node>::iterator it = d_cardinalityVars.find(bag);
  if (it != d_cardinalityVars.end())
  {
    return it->second;
  }
  NodeManager* nm = nodeManager();
  Node x;
  // Reuse the cardinality variable of the input when there is one, i.e. the
  // skolem registered for the term (bag.card bag). That skolem is a purified
  // form of (bag.card bag), so it denotes the cardinality of bag in every
  // context and needs no guard.
  //
  // Note the lookup is for bag itself and not for its representative. The
  // bags of an equivalence class must not share a slot: sharing only holds in
  // the contexts where they are equal, whereas the slots are asserted by a
  // lemma that outlives them. A bag that is equal to the term the cardinality
  // term was registered for keeps its own slot, which the body of the star
  // ties to that one through their (guarded) equality atom.
  Node card = nm->mkNode(Kind::BAG_CARD, bag);
  const std::map<Node, Node>& cardTerms = d_state.getCardinalityTerms();
  std::map<Node, Node>::const_iterator cardIt = cardTerms.find(card);
  if (cardIt != cardTerms.end())
  {
    x = cardIt->second;
  }
  else
  {
    // a placeholder slot, only constrained by the star
    x = nm->getSkolemManager()->mkSkolemFunction(
        SkolemId::BAGS_LIASTAR_BAG_INTEGER, {bag});
  }
  d_cardinalityVars[bag] = x;
  return x;
}

Node BagSolver::getBagBoundVar(const Node& bag)
{
  Assert(bag.getType().isBag());
  std::map<Node, Node>::iterator it = d_bagBoundVars.find(bag);
  if (it != d_bagBoundVars.end())
  {
    return it->second;
  }
  BoundVarManager* bvm = nodeManager()->getBoundVarManager();
  // The variable is named after the bag it is the count of, e.g.
  // count_(bag.inter_min A B), so that the body of the star can be read
  // against the input. A lambda may bind dozens of these variables, so the
  // name of a large bag term is cut short and made unique again by its id.
  std::stringstream term;
  term << bag;
  std::stringstream name;
  name << "count_";
  if (term.str().size() <= 40)
  {
    name << term.str();
  }
  else
  {
    name << term.str().substr(0, 40) << "..." << bag.getId();
  }
  Node c = bvm->mkBoundVar(BoundVarId::BAGS_LIASTAR_BAG_COUNT,
                           bag,
                           name.str(),
                           nodeManager()->integerType());
  d_bagBoundVars[bag] = c;
  if (hasPointwiseTranslation(bag.getKind()))
  {
    // the pointwise definition of bag needs the slots of its arguments
    for (const Node& child : bag)
    {
      getBagBoundVar(child);
    }
  }
  else if (bag.getKind() == Kind::BAG_MAKE)
  {
    // the constraints of a constructed bag are stated over the slots of its
    // singleton and of their difference. See addBagMakeConstraints.
    Node singleton = getBagMakeSingleton(bag);
    if (singleton != bag)
    {
      getBagBoundVar(singleton);
      getBagBoundVar(getBagMakeDifference(bag));
    }
  }
  return c;
}

void BagSolver::addBagMakeConstraints(const Node& bag,
                                      std::vector<Node>& constraints)
{
  Assert(bag.getKind() == Kind::BAG_MAKE);
  Node singleton = getBagMakeSingleton(bag);
  if (singleton == bag)
  {
    // bag is its own singleton, and its cardinality, which
    // addBagMakeCardinalities asserts to be 1, already concentrates its count
    // on one summand of the star
    return;
  }
  NodeManager* nm = nodeManager();
  Node c = d_bagBoundVars[bag];
  Node cSingleton = d_bagBoundVars[singleton];
  Node cDifference = d_bagBoundVars[getBagMakeDifference(bag)];
  // (bag e n) has no element besides the one of (bag e 1), since their
  // difference_remove is the empty bag
  constraints.push_back(cDifference.eqNode(d_zero));
  if (bag[1].isConst() && bag[1].getConst<Rational>().sgn() > 0)
  {
    // (bag e 1) is a subbag of (bag e n) for a positive n. This conjunct is
    // implied by the constraint above and the cardinalities, and is kept as a
    // redundant constraint for the solver.
    constraints.push_back(nm->mkNode(Kind::LEQ, cSingleton, c));
  }
}

void BagSolver::addBagMakeCardinalities()
{
  NodeManager* nm = nodeManager();
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    Node bag = pair.first;
    if (bag.getKind() != Kind::BAG_MAKE)
    {
      continue;
    }
    // the cardinality of (bag e n) is n for a positive n, and 0 otherwise
    Node n = bag[1];
    Node isPositive = nm->mkNode(Kind::GEQ, n, d_one);
    Node card = nm->mkNode(Kind::ITE, isPositive, n, d_zero);
    Node x = getCardinalityVar(bag);
    Node lemma = x.eqNode(card);
    Trace("bags-liastar") << "cardinality of " << bag << ": " << lemma
                          << std::endl;
    d_im.addPendingLemma(lemma, InferenceId::BAGS_LIASTAR);
  }
}

void BagSolver::addBagMakeOverlaps(std::vector<Node>& constraints,
                                   std::vector<Node>& premises)
{
  NodeManager* nm = nodeManager();
  // the distinct singletons of the constructed bags of the star, in the order
  // of d_bagBoundVars, which is fixed
  std::vector<Node> singletons;
  for (const std::pair<const Node, Node>& pair : d_bagBoundVars)
  {
    if (pair.first.getKind() != Kind::BAG_MAKE)
    {
      continue;
    }
    Node singleton = getBagMakeSingleton(pair.first);
    if (std::find(singletons.begin(), singletons.end(), singleton)
        == singletons.end())
    {
      singletons.push_back(singleton);
    }
  }
  for (size_t i = 0, size = singletons.size(); i < size; i++)
  {
    for (size_t j = i + 1; j < size; j++)
    {
      Node x = singletons[i][0];
      Node y = singletons[j][0];
      Node cx = d_bagBoundVars[singletons[i]];
      Node cy = d_bagBoundVars[singletons[j]];
      if (d_state.areDisequal(x, y))
      {
        // the two singletons have no element in common, and each count is 0
        // or 1, so they cannot both be 1 at the same element
        Node sum = nm->mkNode(Kind::ADD, cx, cy);
        constraints.push_back(nm->mkNode(Kind::LEQ, sum, d_one));
        premises.push_back(x.eqNode(y).notNode());
      }
      else if (d_state.areEqual(x, y))
      {
        // the two singletons are the same bag
        constraints.push_back(cx.eqNode(cy));
        premises.push_back(x.eqNode(y));
      }
    }
  }
}

Node BagSolver::getBagMakeSingleton(const Node& bag)
{
  Assert(bag.getKind() == Kind::BAG_MAKE);
  // note this is bag itself when its multiplicity is the constant 1
  return nodeManager()->mkNode(Kind::BAG_MAKE, bag[0], d_one);
}

Node BagSolver::getBagMakeDifference(const Node& bag)
{
  Assert(bag.getKind() == Kind::BAG_MAKE);
  Node singleton = getBagMakeSingleton(bag);
  Assert(singleton != bag);
  // The term is deliberately not rewritten. The rewriter only knows that a
  // difference_remove is empty when its arguments are syntactically equal, so
  // it leaves this term alone, but were it to recognize that this one is empty
  // too, the pointwise definition of the rewritten term would no longer relate
  // the counts of bag and of its singleton, which is the point of the term.
  return nodeManager()->mkNode(Kind::BAG_DIFFERENCE_REMOVE, bag, singleton);
}

Node BagSolver::getPointwiseConstraint(const Node& bag)
{
  Assert(hasPointwiseTranslation(bag.getKind()));
  NodeManager* nm = nodeManager();
  Node c = d_bagBoundVars[bag];
  if (bag.getKind() == Kind::BAG_EMPTY)
  {
    // bag.empty(e) = 0
    return c.eqNode(d_zero);
  }
  Node c1 = d_bagBoundVars[bag[0]];
  if (bag.getKind() == Kind::BAG_SETOF)
  {
    // (bag.setof A)(e) = ite(1 <= A(e), 1, 0)
    Node ite =
        nm->mkNode(Kind::ITE, nm->mkNode(Kind::LEQ, d_one, c1), d_one, d_zero);
    return c.eqNode(ite);
  }
  Node c2 = d_bagBoundVars[bag[1]];
  Node leq = nm->mkNode(Kind::LEQ, c1, c2);
  switch (bag.getKind())
  {
    case Kind::BAG_UNION_DISJOINT:
      // (bag.union_disjoint A B)(e) = A(e) + B(e)
      return c.eqNode(nm->mkNode(Kind::ADD, c1, c2));
    case Kind::BAG_UNION_MAX:
      // (bag.union_max A B)(e) = max(A(e), B(e))
      return c.eqNode(nm->mkNode(Kind::ITE, leq, c2, c1));
    case Kind::BAG_INTER_MIN:
      // (bag.inter_min A B)(e) = min(A(e), B(e))
      return c.eqNode(nm->mkNode(Kind::ITE, leq, c1, c2));
    case Kind::BAG_DIFFERENCE_SUBTRACT:
      // (bag.difference_subtract A B)(e) = max(0, A(e) - B(e)). The
      // truncation matters: a count is non negative.
      return c.eqNode(
          nm->mkNode(Kind::ITE, leq, d_zero, nm->mkNode(Kind::SUB, c1, c2)));
    case Kind::BAG_DIFFERENCE_REMOVE:
      // (bag.difference_remove A B)(e) = ite(B(e) = 0, A(e), 0), i.e. every
      // occurrence of e is removed, not just as many as e occurs in B.
      return c.eqNode(nm->mkNode(Kind::ITE, c2.eqNode(d_zero), c1, d_zero));
    default: Unreachable() << "no pointwise translation for " << bag;
  }
  return Node::null();
}

bool BagSolver::hasPointwiseTranslation(Kind k)
{
  switch (k)
  {
    case Kind::BAG_EMPTY:
    case Kind::BAG_UNION_DISJOINT:
    case Kind::BAG_UNION_MAX:
    case Kind::BAG_INTER_MIN:
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE:
    case Kind::BAG_SETOF: return true;
    // Note (bag x c) is missing on purpose: its count at an element is not a
    // function of the counts of its arguments, it is c at x and 0 everywhere
    // else.
    default: return false;
  }
}

void BagSolver::checkQuantifiedOperations()
{
  for (const Node& bag : d_state.getBags())
  {
    // iterate through all bags terms in each equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case Kind::BAG_MAP: checkMap(n); break;
        default: break;
      }
      it++;
    }
  }

  // add non negative constraints for all multiplicities
  for (const Node& n : d_state.getBags())
  {
    for (const Node& e : d_state.getElements(n))
    {
      checkNonNegativeCountTerms(n, d_state.getRepresentative(e));
    }
  }
}

set<Node> BagSolver::getElementsForBinaryOperator(const Node& n)
{
  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards0 = d_state.getElements(n[0]);
  const set<Node>& upwards1 = d_state.getElements(n[1]);

  set_union(downwards.begin(),
            downwards.end(),
            upwards0.begin(),
            upwards0.end(),
            inserter(elements, elements.begin()));
  elements.insert(upwards1.begin(), upwards1.end());
  return elements;
}

void BagSolver::checkEmpty(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_EMPTY);
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.empty(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionDisjoint(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionDisjoint(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionMax(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionMax(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkIntersectionMin(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_INTER_MIN);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.intersection(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDifferenceSubtract(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceSubtract(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

bool BagSolver::checkBagMake()
{
  bool sentLemma = false;
  for (const Node& bag : d_state.getBags())
  {
    TypeNode bagType = bag.getType();
    NodeManager* nm = nodeManager();
    Node empty = nm->mkConst(EmptyBag(bagType));
    if (d_state.areEqual(empty, bag) || d_state.areDisequal(empty, bag))
    {
      continue;
    }

    // look for BAG_MAKE terms in the equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      if (n.getKind() == Kind::BAG_MAKE)
      {
        Trace("bags-check") << "splitting on node " << std::endl;
        InferInfo i = d_ig.bagMake(n);
        sentLemma |= d_im.lemmaTheoryInference(&i);
        // it is enough to split only once per equivalent class
        break;
      }
      it++;
    }
  }
  return sentLemma;
}

void BagSolver::checkBagMake(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  Trace("bags::BagSolver::postCheck")
      << "BagSolver::checkBagMake Elements of " << n
      << " are: " << d_state.getElements(n) << std::endl;
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.bagMake(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}
void BagSolver::checkNonNegativeCountTerms(const Node& bag, const Node& element)
{
  InferInfo i = d_ig.nonNegativeCount(bag, element);
  d_im.lemmaTheoryInference(&i);
}

void BagSolver::checkDifferenceRemove(const Node& n)
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_REMOVE);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceRemove(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkSetof(Node n)
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[0]);

  elements.insert(downwards.begin(), downwards.end());
  elements.insert(upwards.begin(), upwards.end());

  for (const Node& e : elements)
  {
    InferInfo i = d_ig.setof(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDisequalBagTerms()
{
  for (const auto& [equality, witness] : d_state.getDisequalBagTerms())
  {
    InferInfo info = d_ig.bagDisequality(equality, witness);
    d_im.lemmaTheoryInference(&info);
  }
}

void BagSolver::checkMap(Node n)
{
  Assert(n.getKind() == Kind::BAG_MAP);
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  for (const Node& x : upwards)
  {
    InferInfo upInference = d_ig.mapUp1(n, x);
    d_im.lemmaTheoryInference(&upInference);
  }

  if (d_state.isInjective(n[0]))
  {
    for (const Node& z : downwards)
    {
      InferInfo upInference = d_ig.mapDownInjective(n, z);
      d_im.lemmaTheoryInference(&upInference);
    }
  }
  else
  {
    for (const Node& z : downwards)
    {
      Node y = d_state.getRepresentative(z);
      if (!d_mapCache.count(n))
      {
        std::shared_ptr<context::CDHashMap<Node, std::pair<Node, Node>>> nMap =
            std::make_shared<context::CDHashMap<Node, std::pair<Node, Node>>>(
                userContext());
        d_mapCache[n] = nMap;
      }
      if (!d_mapCache[n].get()->count(y))
      {
        auto [downInference, uf, preImageSize] = d_ig.mapDown(n, y);
        d_im.lemmaTheoryInference(&downInference);
        std::pair<Node, Node> yPair = std::make_pair(uf, preImageSize);
        d_mapCache[n].get()->insert(y, yPair);
      }

      context::CDHashMap<Node, std::pair<Node, Node>>::iterator it =
          d_mapCache[n].get()->find(y);

      auto [uf, preImageSize] = it->second;

      for (const Node& x : upwards)
      {
        InferInfo upInference = d_ig.mapUp2(n, uf, preImageSize, y, x);
        d_im.lemmaTheoryInference(&upInference);
      }
    }
  }
}

void BagSolver::checkFilter(Node n)
{
  Assert(n.getKind() == Kind::BAG_FILTER);

  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  elements.insert(downwards.begin(), downwards.end());
  elements.insert(upwards.begin(), upwards.end());

  for (const Node& e : elements)
  {
    InferInfo i = d_ig.filterDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.filterUp(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkProduct(Node n)
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  const set<Node>& elementsA = d_state.getElements(n[0]);
  const set<Node>& elementsB = d_state.getElements(n[1]);

  for (const Node& e1 : elementsA)
  {
    for (const Node& e2 : elementsB)
    {
      InferInfo i = d_ig.productUp(
          n, d_state.getRepresentative(e1), d_state.getRepresentative(e2));
      d_im.lemmaTheoryInference(&i);
    }
  }

  std::set<Node> elements = d_state.getElements(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.productDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkJoin(Node n)
{
  Assert(n.getKind() == Kind::TABLE_JOIN);
  const set<Node>& elementsA = d_state.getElements(n[0]);
  const set<Node>& elementsB = d_state.getElements(n[1]);

  for (const Node& e1 : elementsA)
  {
    for (const Node& e2 : elementsB)
    {
      InferInfo i = d_ig.joinUp(
          n, d_state.getRepresentative(e1), d_state.getRepresentative(e2));
      d_im.lemmaTheoryInference(&i);
    }
  }

  std::set<Node> elements = d_state.getElements(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.joinDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkGroup(Node n)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);

  InferInfo notEmpty = d_ig.groupNotEmpty(n);
  d_im.lemmaTheoryInference(&notEmpty);

  Node part = d_ig.defineSkolemPartFunction(n);

  const set<Node>& elementsA = d_state.getElements(n[0]);
  std::shared_ptr<context::CDHashSet<Node>> skolems =
      d_state.getPartElementSkolems(n);
  for (const Node& a : elementsA)
  {
    if (skolems->contains(a))
    {
      // skip skolem elements that were introduced by groupPartCount below.
      continue;
    }
    Node aRep = d_state.getRepresentative(a);
    InferInfo i = d_ig.groupUp1(n, aRep, part);
    d_im.lemmaTheoryInference(&i);
    i = d_ig.groupUp2(n, aRep, part);
    d_im.lemmaTheoryInference(&i);
  }

  std::set<Node> parts = d_state.getElements(n);
  for (std::set<Node>::iterator partIt1 = parts.begin(); partIt1 != parts.end();
       ++partIt1)
  {
    Node part1 = d_state.getRepresentative(*partIt1);
    std::vector<Node> partEqc;
    d_state.getEquivalenceClass(part1, partEqc);
    bool newPart = true;
    for (Node p : partEqc)
    {
      if (p.getKind() == Kind::APPLY_UF && p.getOperator() == part)
      {
        newPart = false;
      }
    }
    if (newPart)
    {
      // only apply the groupPartCount rule for a part that does not have
      // nodes of the form (part x) introduced by the group up rule above.
      InferInfo partCardinality = d_ig.groupPartCount(n, part1, part);
      d_im.lemmaTheoryInference(&partCardinality);
    }

    std::set<Node> partElements = d_state.getElements(part1);
    for (std::set<Node>::iterator i = partElements.begin();
         i != partElements.end();
         ++i)
    {
      Node x = d_state.getRepresentative(*i);
      if (!skolems->contains(x))
      {
        // only apply down rules for elements not generated by groupPartCount
        // rule above
        InferInfo down = d_ig.groupDown(n, part1, x, part);
        d_im.lemmaTheoryInference(&down);
      }

      std::set<Node>::iterator j = i;
      ++j;
      while (j != partElements.end())
      {
        Node y = d_state.getRepresentative(*j);
        // x, y should have the same projection
        InferInfo sameProjection =
            d_ig.groupSameProjection(n, part1, x, y, part);
        d_im.lemmaTheoryInference(&sameProjection);
        ++j;
      }

      for (const Node& a : elementsA)
      {
        Node y = d_state.getRepresentative(a);
        if (x != y)
        {
          // x, y should have the same projection
          InferInfo samePart = d_ig.groupSamePart(n, part1, x, y, part);
          d_im.lemmaTheoryInference(&samePart);
        }
      }
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
