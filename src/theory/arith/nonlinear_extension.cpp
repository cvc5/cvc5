/*********************                                                        */
/*! \file nonlinear_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/nonlinear_extension.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/ext_theory.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

namespace {

// Return true if a collection c contains an elem k. Compatible with map and set
// containers.
template <class Container, class Key>
bool Contains(const Container& c, const Key& k) {
  return c.find(k) != c.end();
}

// Inserts value into the set/map c if the value was not present there. Returns
// true if the value was inserted.
template <class Container, class Value>
bool InsertIfNotPresent(Container* c, const Value& value) {
  return (c->insert(value)).second;
}

// Returns true if a vector c contains an elem t.
template <class T>
bool IsInVector(const std::vector<T>& c, const T& t) {
  return std::find(c.begin(), c.end(), t) != c.end();
}

// Returns the a[key] and assertion fails in debug mode.
inline unsigned getCount(const NodeMultiset& a, Node key) {
  NodeMultiset::const_iterator it = a.find(key);
  Assert(it != a.end());
  return it->second;
}

// Returns a[key] if key is in a or value otherwise.
unsigned getCountWithDefault(const NodeMultiset& a, Node key, unsigned value) {
  NodeMultiset::const_iterator it = a.find(key);
  return (it == a.end()) ? value : it->second;
}

// Returns true if for any key then a[key] <= b[key] where the value for any key
// not present is interpreted as 0.
bool isSubset(const NodeMultiset& a, const NodeMultiset& b) {
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a) {
    Node key = it_a->first;
    const unsigned a_value = it_a->second;
    const unsigned b_value = getCountWithDefault(b, key, 0);
    if (a_value > b_value) {
      return false;
    }
  }
  return true;
}

// Given two multisets return the multiset difference a \ b.
NodeMultiset diffMultiset(const NodeMultiset& a, const NodeMultiset& b) {
  NodeMultiset difference;
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a) {
    Node key = it_a->first;
    const unsigned a_value = it_a->second;
    const unsigned b_value = getCountWithDefault(b, key, 0);
    if (a_value > b_value) {
      difference[key] = a_value - b_value;
    }
  }
  return difference;
}

// Return a vector containing a[key] repetitions of key in a multiset a.
std::vector<Node> ExpandMultiset(const NodeMultiset& a) {
  std::vector<Node> expansion;
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a) {
    expansion.insert(expansion.end(), it_a->second, it_a->first);
  }
  return expansion;
}

void debugPrintBound(const char* c, Node coeff, Node x, Kind type, Node rhs) {
  Node t = ArithMSum::mkCoeffTerm(coeff, x);
  Trace(c) << t << " " << type << " " << rhs;
}

struct SortNlModel
{
  SortNlModel()
      : d_nlm(nullptr),
        d_isConcrete(true),
        d_isAbsolute(false),
        d_reverse_order(false)
  {
  }
  /** pointer to the model */
  NlModel* d_nlm;
  /** are we comparing concrete model values? */
  bool d_isConcrete;
  /** are we comparing absolute values? */
  bool d_isAbsolute;
  /** are we in reverse order? */
  bool d_reverse_order;
  /** the comparison */
  bool operator()(Node i, Node j) {
    int cv = d_nlm->compare(i, j, d_isConcrete, d_isAbsolute);
    if (cv == 0) {
      return i < j;
    }
    return d_reverse_order ? cv < 0 : cv > 0;
  }
};
struct SortNonlinearDegree
{
  SortNonlinearDegree(NodeMultiset& m) : d_mdegree(m) {}
  /** pointer to the non-linear extension */
  NodeMultiset& d_mdegree;
  /**
   * Sorts by degree of the monomials, where lower degree monomials come
   * first.
   */
  bool operator()(Node i, Node j)
  {
    unsigned i_count = getCount(d_mdegree, i);
    unsigned j_count = getCount(d_mdegree, j);
    return i_count == j_count ? (i < j) : (i_count < j_count ? true : false);
  }
};

bool hasNewMonomials(Node n, const std::vector<Node>& existing) {
  std::set<Node> visited;

  std::vector<Node> worklist;
  worklist.push_back(n);
  while (!worklist.empty()) {
    Node current = worklist.back();
    worklist.pop_back();
    if (!Contains(visited, current)) {
      visited.insert(current);
      if (current.getKind() == NONLINEAR_MULT)
      {
        if (!IsInVector(existing, current)) {
          return true;
        }
      } else {
        worklist.insert(worklist.end(), current.begin(), current.end());
      }
    }
  }
  return false;
}

}  // namespace

NonlinearExtension::NonlinearExtension(TheoryArith& containing,
                                       eq::EqualityEngine* ee)
    : d_lemmas(containing.getUserContext()),
      d_zero_split(containing.getUserContext()),
      d_containing(containing),
      d_ee(ee),
      d_needsLastCall(false),
      d_model(containing.getSatContext()),
      d_builtModel(containing.getSatContext(), false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_two = NodeManager::currentNM()->mkConst(Rational(2));
  d_order_points.push_back(d_neg_one);
  d_order_points.push_back(d_zero);
  d_order_points.push_back(d_one);
  d_taylor_real_fv = NodeManager::currentNM()->mkBoundVar(
      "x", NodeManager::currentNM()->realType());
  d_taylor_real_fv_base = NodeManager::currentNM()->mkBoundVar(
      "a", NodeManager::currentNM()->realType());
  d_taylor_real_fv_base_rem = NodeManager::currentNM()->mkBoundVar(
      "b", NodeManager::currentNM()->realType());
  d_taylor_degree = options::nlExtTfTaylorDegree();
}

NonlinearExtension::~NonlinearExtension() {}

// Returns a reference to either map[key] if it exists in the map
// or to a default value otherwise.
//
// Warning: sped_cial care must be taken if value is a temporary object.
template <class MapType, class Key, class Value>
const Value& FindWithDefault(const MapType& map, const Key& key,
                             const Value& value) {
  typename MapType::const_iterator it = map.find(key);
  if (it == map.end()) {
    return value;
  }
  return it->second;
}

const NodeMultiset& NonlinearExtension::getMonomialExponentMap(
    Node monomial) const {
  MonomialExponentMap::const_iterator it = d_m_exp.find(monomial);
  Assert(it != d_m_exp.end());
  return it->second;
}

bool NonlinearExtension::isMonomialSubset(Node a, Node b) const {
  const NodeMultiset& a_exponent_map = getMonomialExponentMap(a);
  const NodeMultiset& b_exponent_map = getMonomialExponentMap(b);

  return isSubset(a_exponent_map, b_exponent_map);
}

void NonlinearExtension::registerMonomialSubset(Node a, Node b) {
  Assert(isMonomialSubset(a, b));

  const NodeMultiset& a_exponent_map = getMonomialExponentMap(a);
  const NodeMultiset& b_exponent_map = getMonomialExponentMap(b);

  std::vector<Node> diff_children =
      ExpandMultiset(diffMultiset(b_exponent_map, a_exponent_map));
  Assert(!diff_children.empty());

  d_m_contain_parent[a].push_back(b);
  d_m_contain_children[b].push_back(a);

  Node mult_term = safeConstructNary(MULT, diff_children);
  Node nlmult_term = safeConstructNary(NONLINEAR_MULT, diff_children);
  d_m_contain_mult[a][b] = mult_term;
  d_m_contain_umult[a][b] = nlmult_term;
  Trace("nl-ext-mindex") << "..." << a << " is a subset of " << b
                         << ", difference is " << mult_term << std::endl;
}

bool NonlinearExtension::getCurrentSubstitution(
    int effort, const std::vector<Node>& vars, std::vector<Node>& subs,
    std::map<Node, std::vector<Node> >& exp) {
  // get the constant equivalence classes
  std::map<Node, std::vector<int> > rep_to_subs_index;

  bool retVal = false;
  for (unsigned i = 0; i < vars.size(); i++) {
    Node n = vars[i];
    if (d_ee->hasTerm(n)) {
      Node nr = d_ee->getRepresentative(n);
      if (nr.isConst()) {
        subs.push_back(nr);
        Trace("nl-subs") << "Basic substitution : " << n << " -> " << nr
                         << std::endl;
        exp[n].push_back(n.eqNode(nr));
        retVal = true;
      } else {
        rep_to_subs_index[nr].push_back(i);
        subs.push_back(n);
      }
    } else {
      subs.push_back(n);
    }
  }

  // return true if the substitution is non-trivial
  return retVal;

  // d_containing.getValuation().getModel()->getRepresentative( n );
}

std::pair<bool, Node> NonlinearExtension::isExtfReduced(
    int effort, Node n, Node on, const std::vector<Node>& exp) const {
  if (n != d_zero) {
    Kind k = n.getKind();
    return std::make_pair(k != NONLINEAR_MULT && !isTranscendentalKind(k),
                          Node::null());
  }
  Assert(n == d_zero);
  if (on.getKind() == NONLINEAR_MULT)
  {
    Trace("nl-ext-zero-exp") << "Infer zero : " << on << " == " << n
                             << std::endl;
    // minimize explanation if a substitution+rewrite results in zero
    const std::set<Node> vars(on.begin(), on.end());

    for (unsigned i = 0, size = exp.size(); i < size; i++)
    {
      Trace("nl-ext-zero-exp") << "  exp[" << i << "] = " << exp[i]
                               << std::endl;
      std::vector<Node> eqs;
      if (exp[i].getKind() == EQUAL)
      {
        eqs.push_back(exp[i]);
      }
      else if (exp[i].getKind() == AND)
      {
        for (const Node& ec : exp[i])
        {
          if (ec.getKind() == EQUAL)
          {
            eqs.push_back(ec);
          }
        }
      }

      for (unsigned j = 0; j < eqs.size(); j++)
      {
        for (unsigned r = 0; r < 2; r++)
        {
          if (eqs[j][r] == d_zero && vars.find(eqs[j][1 - r]) != vars.end())
          {
            Trace("nl-ext-zero-exp") << "...single exp : " << eqs[j]
                                     << std::endl;
            return std::make_pair(true, eqs[j]);
          }
        }
      }
    }
  }
  return std::make_pair(true, Node::null());
}

void NonlinearExtension::registerMonomial(Node n) {
  if (!IsInVector(d_monomials, n)) {
    d_monomials.push_back(n);
    Trace("nl-ext-debug") << "Register monomial : " << n << std::endl;
    if (n.getKind() == NONLINEAR_MULT)
    {
      // get exponent count
      for (unsigned k = 0; k < n.getNumChildren(); k++) {
        d_m_exp[n][n[k]]++;
        if (k == 0 || n[k] != n[k - 1]) {
          d_m_vlist[n].push_back(n[k]);
        }
      }
      d_m_degree[n] = n.getNumChildren();
    } else if (n == d_one) {
      d_m_exp[n].clear();
      d_m_vlist[n].clear();
      d_m_degree[n] = 0;
    } else {
      Assert(!isArithKind(n.getKind()));
      d_m_exp[n][n] = 1;
      d_m_vlist[n].push_back(n);
      d_m_degree[n] = 1;
    }
    // TODO: sort necessary here?
    std::sort(d_m_vlist[n].begin(), d_m_vlist[n].end());
    Trace("nl-ext-mindex") << "Add monomial to index : " << n << std::endl;
    d_m_index.addTerm(n, d_m_vlist[n], this);
  }
}

void NonlinearExtension::setMonomialFactor(Node a, Node b,
                                           const NodeMultiset& common) {
  // Could not tell if this was being inserted intentionally or not.
  std::map<Node, Node>& mono_diff_a = d_mono_diff[a];
  if (!Contains(mono_diff_a, b)) {
    Trace("nl-ext-mono-factor")
        << "Set monomial factor for " << a << "/" << b << std::endl;
    mono_diff_a[b] = mkMonomialRemFactor(a, common);
  }
}

void NonlinearExtension::registerConstraint(Node atom) {
  if (!IsInVector(d_constraints, atom)) {
    d_constraints.push_back(atom);
    Trace("nl-ext-debug") << "Register constraint : " << atom << std::endl;
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(atom, msum))
    {
      Trace("nl-ext-debug") << "got monomial sum: " << std::endl;
      if (Trace.isOn("nl-ext-debug")) {
        ArithMSum::debugPrintMonomialSum(msum, "nl-ext-debug");
      }
      unsigned max_degree = 0;
      std::vector<Node> all_m;
      std::vector<Node> max_deg_m;
      for (std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end();
           ++itm) {
        if (!itm->first.isNull()) {
          all_m.push_back(itm->first);
          registerMonomial(itm->first);
          Trace("nl-ext-debug2")
              << "...process monomial " << itm->first << std::endl;
          Assert(d_m_degree.find(itm->first) != d_m_degree.end());
          unsigned d = d_m_degree[itm->first];
          if (d > max_degree) {
            max_degree = d;
            max_deg_m.clear();
          }
          if (d >= max_degree) {
            max_deg_m.push_back(itm->first);
          }
        }
      }
      // isolate for each maximal degree monomial
      for (unsigned i = 0; i < all_m.size(); i++) {
        Node m = all_m[i];
        Node rhs, coeff;
        int res = ArithMSum::isolate(m, msum, coeff, rhs, atom.getKind());
        if (res != 0) {
          Kind type = atom.getKind();
          if (res == -1) {
            type = reverseRelationKind(type);
          }
          Trace("nl-ext-constraint") << "Constraint : " << atom << " <=> ";
          if (!coeff.isNull()) {
            Trace("nl-ext-constraint") << coeff << " * ";
          }
          Trace("nl-ext-constraint")
              << m << " " << type << " " << rhs << std::endl;
          d_c_info[atom][m].d_rhs = rhs;
          d_c_info[atom][m].d_coeff = coeff;
          d_c_info[atom][m].d_type = type;
        }
      }
      for (unsigned i = 0; i < max_deg_m.size(); i++) {
        Node m = max_deg_m[i];
        d_c_info_maxm[atom][m] = true;
      }
    } else {
      Trace("nl-ext-debug") << "...failed to get monomial sum." << std::endl;
    }
  }
}

bool NonlinearExtension::isArithKind(Kind k) {
  return k == PLUS || k == MULT || k == NONLINEAR_MULT;
}

Node NonlinearExtension::mkLit(Node a, Node b, int status, bool isAbsolute)
{
  if (status == 0) {
    Node a_eq_b = a.eqNode(b);
    if (!isAbsolute)
    {
      return a_eq_b;
    }
    else
    {
      // return mkAbs( a ).eqNode( mkAbs( b ) );
      Node negate_b = NodeManager::currentNM()->mkNode(UMINUS, b);
      return a_eq_b.orNode(a.eqNode(negate_b));
    }
  } else if (status < 0) {
    return mkLit(b, a, -status);
  } else {
    Assert(status == 1 || status == 2);
    NodeManager* nm = NodeManager::currentNM();
    Kind greater_op = status == 1 ? GEQ : GT;
    if (!isAbsolute)
    {
      return nm->mkNode(greater_op, a, b);
    }
    else
    {
      // return nm->mkNode( greater_op, mkAbs( a ), mkAbs( b ) );
      Node zero = mkRationalNode(0);
      Node a_is_nonnegative = nm->mkNode(GEQ, a, zero);
      Node b_is_nonnegative = nm->mkNode(GEQ, b, zero);
      Node negate_a = nm->mkNode(UMINUS, a);
      Node negate_b = nm->mkNode(UMINUS, b);
      return a_is_nonnegative.iteNode(
          b_is_nonnegative.iteNode(nm->mkNode(greater_op, a, b),
                                   nm->mkNode(greater_op, a, negate_b)),
          b_is_nonnegative.iteNode(nm->mkNode(greater_op, negate_a, b),
                                   nm->mkNode(greater_op, negate_a, negate_b)));
    }
  }
}

Node NonlinearExtension::mkAbs(Node a) {
  if (a.isConst()) {
    return mkRationalNode(a.getConst<Rational>().abs());
  } else {
    NodeManager* nm = NodeManager::currentNM();
    Node a_is_nonnegative = nm->mkNode(GEQ, a, mkRationalNode(0));
    return a_is_nonnegative.iteNode(a, nm->mkNode(UMINUS, a));
  }
}

Node NonlinearExtension::mkValidPhase(Node a, Node pi) {
  return mkBounded(
      NodeManager::currentNM()->mkNode(MULT, mkRationalNode(-1), pi), a, pi);
}

Node NonlinearExtension::mkBounded( Node l, Node a, Node u ) {
  return NodeManager::currentNM()->mkNode(
      AND,
      NodeManager::currentNM()->mkNode(GEQ, a, l),
      NodeManager::currentNM()->mkNode(LEQ, a, u));
}

Node NonlinearExtension::mkMonomialRemFactor(
    Node n, const NodeMultiset& n_exp_rem) const {
  std::vector<Node> children;
  const NodeMultiset& exponent_map = getMonomialExponentMap(n);
  for (NodeMultiset::const_iterator itme2 = exponent_map.begin();
       itme2 != exponent_map.end(); ++itme2) {
    Node v = itme2->first;
    unsigned inc = itme2->second;
    Trace("nl-ext-mono-factor")
        << "..." << inc << " factors of " << v << std::endl;
    unsigned count_in_n_exp_rem = getCountWithDefault(n_exp_rem, v, 0);
    Assert(count_in_n_exp_rem <= inc);
    inc -= count_in_n_exp_rem;
    Trace("nl-ext-mono-factor")
        << "......rem, now " << inc << " factors of " << v << std::endl;
    children.insert(children.end(), inc, v);
  }
  Node ret = safeConstructNary(MULT, children);
  ret = Rewriter::rewrite(ret);
  Trace("nl-ext-mono-factor") << "...return : " << ret << std::endl;
  return ret;
}

void NonlinearExtension::sendLemmas(const std::vector<Node>& out,
                                    bool preprocess,
                                    std::map<Node, NlLemmaSideEffect>& lemSE)
{
  std::map<Node, NlLemmaSideEffect>::iterator its;
  for (const Node& lem : out)
  {
    Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : " << lem << std::endl;
    d_containing.getOutputChannel().lemma(lem, false, preprocess);
    // process the side effect
    its = lemSE.find(lem);
    if (its != lemSE.end())
    {
      processSideEffect(its->second);
    }
    // add to cache if not preprocess
    if (!preprocess)
    {
      d_lemmas.insert(lem);
    }
    // also indicate this is a tautology
    d_model.addTautology(lem);
  }
}

void NonlinearExtension::processSideEffect(const NlLemmaSideEffect& se)
{
  for (const std::tuple<Node, unsigned, Node>& sp : se.d_secantPoint)
  {
    Node tf = std::get<0>(sp);
    unsigned d = std::get<1>(sp);
    Node c = std::get<2>(sp);
    d_secant_points[tf][d].push_back(c);
  }
}

unsigned NonlinearExtension::filterLemma(Node lem, std::vector<Node>& out)
{
  Trace("nl-ext-lemma-debug")
      << "NonlinearExtension::Lemma pre-rewrite : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if (d_lemmas.find(lem) != d_lemmas.end()
      || std::find(out.begin(), out.end(), lem) != out.end())
  {
    Trace("nl-ext-lemma-debug")
        << "NonlinearExtension::Lemma duplicate : " << lem << std::endl;
    return 0;
  }
  out.push_back(lem);
  return 1;
}

unsigned NonlinearExtension::filterLemmas(std::vector<Node>& lemmas,
                                          std::vector<Node>& out)
{
  if (options::nlExtEntailConflicts())
  {
    // check if any are entailed to be false
    for (const Node& lem : lemmas)
    {
      Node ch_lemma = lem.negate();
      ch_lemma = Rewriter::rewrite(ch_lemma);
      Trace("nl-ext-et-debug")
          << "Check entailment of " << ch_lemma << "..." << std::endl;
      std::pair<bool, Node> et = d_containing.getValuation().entailmentCheck(
          options::TheoryOfMode::THEORY_OF_TYPE_BASED, ch_lemma);
      Trace("nl-ext-et-debug") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
      if (et.first)
      {
        Trace("nl-ext-et") << "*** Lemma entailed to be in conflict : " << lem
                           << std::endl;
        // return just this lemma
        if (filterLemma(lem, out) > 0)
        {
          lemmas.clear();
          return 1;
        }
      }
    }
  }

  unsigned sum = 0;
  for (const Node& lem : lemmas)
  {
    sum += filterLemma(lem, out);
  }
  lemmas.clear();
  return sum;
}

void NonlinearExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("nl-ext") << "Getting assertions..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // get the assertions
  std::map<Node, Rational> init_bounds[2];
  std::map<Node, Node> init_bounds_lit[2];
  unsigned nassertions = 0;
  std::unordered_set<Node, NodeHashFunction> init_assertions;
  for (Theory::assertions_iterator it = d_containing.facts_begin();
       it != d_containing.facts_end();
       ++it)
  {
    nassertions++;
    const Assertion& assertion = *it;
    Node lit = assertion.d_assertion;
    init_assertions.insert(lit);
    // check for concrete bounds
    bool pol = lit.getKind() != NOT;
    Node atom_orig = lit.getKind() == NOT ? lit[0] : lit;

    std::vector<Node> atoms;
    if (atom_orig.getKind() == EQUAL)
    {
      if (pol)
      {
        // t = s  is ( t >= s ^ t <= s )
        for (unsigned i = 0; i < 2; i++)
        {
          Node atom_new = nm->mkNode(GEQ, atom_orig[i], atom_orig[1 - i]);
          atom_new = Rewriter::rewrite(atom_new);
          atoms.push_back(atom_new);
        }
      }
    }
    else
    {
      atoms.push_back(atom_orig);
    }

    for (const Node& atom : atoms)
    {
      // non-strict bounds only
      if (atom.getKind() == GEQ || (!pol && atom.getKind() == GT))
      {
        Node p = atom[0];
        Assert(atom[1].isConst());
        Rational bound = atom[1].getConst<Rational>();
        if (!pol)
        {
          if (atom[0].getType().isInteger())
          {
            // ~( p >= c ) ---> ( p <= c-1 )
            bound = bound - Rational(1);
          }
        }
        unsigned bindex = pol ? 0 : 1;
        bool setBound = true;
        std::map<Node, Rational>::iterator itb = init_bounds[bindex].find(p);
        if (itb != init_bounds[bindex].end())
        {
          if (itb->second == bound)
          {
            setBound = atom_orig.getKind() == EQUAL;
          }
          else
          {
            setBound = pol ? itb->second < bound : itb->second > bound;
          }
          if (setBound)
          {
            // the bound is subsumed
            init_assertions.erase(init_bounds_lit[bindex][p]);
          }
        }
        if (setBound)
        {
          Trace("nl-ext-init") << (pol ? "Lower" : "Upper") << " bound for "
                               << p << " : " << bound << std::endl;
          init_bounds[bindex][p] = bound;
          init_bounds_lit[bindex][p] = lit;
        }
      }
    }
  }
  // for each bound that is the same, ensure we've inferred the equality
  for (std::pair<const Node, Rational>& ib : init_bounds[0])
  {
    Node p = ib.first;
    Node lit1 = init_bounds_lit[0][p];
    if (lit1.getKind() != EQUAL)
    {
      std::map<Node, Rational>::iterator itb = init_bounds[1].find(p);
      if (itb != init_bounds[1].end())
      {
        if (ib.second == itb->second)
        {
          Node eq = p.eqNode(nm->mkConst(ib.second));
          eq = Rewriter::rewrite(eq);
          Node lit2 = init_bounds_lit[1][p];
          Assert(lit2.getKind() != EQUAL);
          // use the equality instead, thus these are redundant
          init_assertions.erase(lit1);
          init_assertions.erase(lit2);
          init_assertions.insert(eq);
        }
      }
    }
  }

  for (const Node& a : init_assertions)
  {
    assertions.push_back(a);
  }
  Trace("nl-ext") << "...keep " << assertions.size() << " / " << nassertions
                  << " assertions." << std::endl;
}

std::vector<Node> NonlinearExtension::checkModelEval(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (size_t i = 0; i < assertions.size(); ++i) {
    Node lit = assertions[i];
    Node atom = lit.getKind()==NOT ? lit[0] : lit;
    Node litv = d_model.computeConcreteModelValue(lit);
    Trace("nl-ext-mv-assert") << "M[[ " << lit << " ]] -> " << litv;
    if (litv != d_true)
    {
      Trace("nl-ext-mv-assert") << " [model-false]" << std::endl;
      false_asserts.push_back(lit);
    }
    else
    {
      Trace("nl-ext-mv-assert") << std::endl;
    }
  }
  return false_asserts;
}

bool NonlinearExtension::checkModel(const std::vector<Node>& assertions,
                                    const std::vector<Node>& false_asserts,
                                    std::vector<Node>& lemmas,
                                    std::vector<Node>& gs)
{
  Trace("nl-ext-cm") << "--- check-model ---" << std::endl;

  // get the presubstitution
  Trace("nl-ext-cm-debug") << "  apply pre-substitution..." << std::endl;
  std::vector<Node> pvars;
  std::vector<Node> psubs;
  for (std::pair<const Node, Node>& tb : d_trMaster)
  {
    pvars.push_back(tb.first);
    psubs.push_back(tb.second);
  }
  // initialize representation of assertions
  std::vector<Node> passertions;
  for (const Node& a : assertions)
  {
    Node pa = a;
    if (!pvars.empty())
    {
      pa = arithSubstitute(pa, pvars, psubs);
      pa = Rewriter::rewrite(pa);
    }
    if (!pa.isConst() || !pa.getConst<bool>())
    {
      Trace("nl-ext-cm-assert") << "- assert : " << pa << std::endl;
      passertions.push_back(pa);
    }
  }

  // get model bounds for all transcendental functions
  Trace("nl-ext-cm") << "----- Get bounds for transcendental functions..."
                     << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_funcMap)
  {
    Kind k = tfs.first;
    for (const Node& tf : tfs.second)
    {
      Trace("nl-ext-cm") << "- Term: " << tf << std::endl;
      bool success = true;
      // tf is Figure 3 : tf( x )
      Node bl;
      Node bu;
      if (k == PI)
      {
        bl = d_pi_bound[0];
        bu = d_pi_bound[1];
      }
      else
      {
        std::pair<Node, Node> bounds = getTfModelBounds(tf, d_taylor_degree);
        bl = bounds.first;
        bu = bounds.second;
        if (bl != bu)
        {
          d_model.setUsedApproximate();
        }
      }
      if (!bl.isNull() && !bu.isNull())
      {
        // for each function in the congruence classe
        for (const Node& ctf : d_funcCongClass[tf])
        {
          // each term in congruence classes should be master terms
          Assert(d_trSlaves.find(ctf) != d_trSlaves.end());
          // we set the bounds for each slave of tf
          for (const Node& stf : d_trSlaves[ctf])
          {
            Trace("nl-ext-cm") << "...bound for " << stf << " : [" << bl << ", "
                               << bu << "]" << std::endl;
            success = d_model.addCheckModelBound(stf, bl, bu);
          }
        }
      }
      else
      {
        Trace("nl-ext-cm") << "...no bound for " << tf << std::endl;
      }
      if (!success)
      {
        // a bound was conflicting
        Trace("nl-ext-cm") << "...failed to set bound for " << tf << std::endl;
        Trace("nl-ext-cm") << "-----" << std::endl;
        return false;
      }
    }
  }
  Trace("nl-ext-cm") << "-----" << std::endl;
  bool ret = d_model.checkModel(
      passertions, false_asserts, d_taylor_degree, lemmas, gs);
  return ret;
}


std::vector<Node> NonlinearExtension::checkSplitZero() {
  std::vector<Node> lemmas;
  for (unsigned i = 0; i < d_ms_vars.size(); i++) {
    Node v = d_ms_vars[i];
    if (d_zero_split.insert(v)) {
      Node eq = v.eqNode(d_zero);
      eq = Rewriter::rewrite(eq);
      Node literal = d_containing.getValuation().ensureLiteral(eq);
      d_containing.getOutputChannel().requirePhase(literal, true);
      lemmas.push_back(literal.orNode(literal.negate()));
    }
  }
  return lemmas;
}

/** An argument trie, for computing congruent terms */
class ArgTrie
{
 public:
  /** children of this node */
  std::map<Node, ArgTrie> d_children;
  /** the data of this node */
  Node d_data;
  /**
   * Set d as the data on the node whose path is [args], return either d if
   * that node has no data, or the data that already occurs there.
   */
  Node add(Node d, const std::vector<Node>& args)
  {
    ArgTrie* at = this;
    for (const Node& a : args)
    {
      at = &(at->d_children[a]);
    }
    if (at->d_data.isNull())
    {
      at->d_data = d;
    }
    return at->d_data;
  }
};

int NonlinearExtension::checkLastCall(const std::vector<Node>& assertions,
                                      const std::vector<Node>& false_asserts,
                                      const std::vector<Node>& xts,
                                      std::vector<Node>& lems,
                                      std::vector<Node>& lemsPp,
                                      std::vector<Node>& wlems,
                                      std::map<Node, NlLemmaSideEffect>& lemSE)
{
  d_ms_vars.clear();
  d_ms_proc.clear();
  d_ms.clear();
  d_mterms.clear();
  d_m_nconst_factor.clear();
  d_tplane_refine.clear();
  d_ci.clear();
  d_ci_exp.clear();
  d_ci_max.clear();
  d_funcCongClass.clear();
  d_funcMap.clear();
  d_tf_region.clear();

  std::vector<Node> lemmas;
  NodeManager* nm = NodeManager::currentNM();

  Trace("nl-ext-mv") << "Extended terms : " << std::endl;
  // register the extended function terms
  std::map< Node, Node > mvarg_to_term;
  std::vector<Node> trNeedsMaster;
  bool needPi = false;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    d_model.computeConcreteModelValue(a);
    d_model.computeAbstractModelValue(a);
    d_model.printModelValue("nl-ext-mv", a);
    Kind ak = a.getKind();
    bool consider = true;
    // if is an unpurified application of SINE, or it is a transcendental
    // applied to a trancendental, purify.
    if (isTranscendentalKind(ak))
    {
      // if we've already computed master for a
      if (d_trMaster.find(a) != d_trMaster.end())
      {
        // a master has at least one slave
        consider = (d_trSlaves.find(a) != d_trSlaves.end());
      }
      else
      {
        if (ak == SINE)
        {
          // always not a master
          consider = false;
        }
        else
        {
          for (const Node& ac : a)
          {
            if (isTranscendentalKind(ac.getKind()))
            {
              consider = false;
              break;
            }
          }
        }
        if (!consider)
        {
          // wait to assign a master below
          trNeedsMaster.push_back(a);
        }
        else
        {
          d_trMaster[a] = a;
          d_trSlaves[a].push_back(a);
        }
      }
    }
    if (ak == NONLINEAR_MULT)
    {
      d_ms.push_back( a );
      
      //context-independent registration
      registerMonomial(a);

      std::map<Node, std::vector<Node> >::iterator itvl = d_m_vlist.find(a);
      Assert(itvl != d_m_vlist.end());
      for (unsigned k = 0; k < itvl->second.size(); k++) {
        if (!IsInVector(d_ms_vars, itvl->second[k])) {
          d_ms_vars.push_back(itvl->second[k]);
        }
        Node mvk = d_model.computeAbstractModelValue(itvl->second[k]);
        if( !mvk.isConst() ){
          d_m_nconst_factor[a] = true;
        }
      }
      // mark processed if has a "one" factor (will look at reduced monomial)?
    }
    else if (a.getNumChildren() > 0)
    {
      if (ak == SINE)
      {
        needPi = true;
      }
      // if we didn't indicate that it should be purified above
      if( consider ){
        std::vector<Node> repList;
        for (const Node& ac : a)
        {
          Node r = d_model.computeConcreteModelValue(ac);
          repList.push_back(r);
        }
        Node aa = argTrie[ak].add(a, repList);
        if (aa != a)
        {
          // apply congruence to pairs of terms that are disequal and congruent
          Assert(aa.getNumChildren() == a.getNumChildren());
          Node mvaa = d_model.computeAbstractModelValue(a);
          Node mvaaa = d_model.computeAbstractModelValue(aa);
          if (mvaa != mvaaa)
          {
            std::vector<Node> exp;
            for (unsigned j = 0, size = a.getNumChildren(); j < size; j++)
            {
              exp.push_back(a[j].eqNode(aa[j]));
            }
            Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
            Node cong_lemma = nm->mkNode(OR, expn.negate(), a.eqNode(aa));
            lemmas.push_back( cong_lemma );
          }
        }
        else
        {
          // new representative of congruence class
          d_funcMap[ak].push_back(a);
        }
        // add to congruence class
        d_funcCongClass[aa].push_back(a);
      }
    }
    else if (ak == PI)
    {
      Assert(consider);
      needPi = true;
      d_funcMap[ak].push_back(a);
      d_funcCongClass[a].push_back(a);
    }
    else
    {
      Assert(false);
    }
  }
  // initialize pi if necessary
  if (needPi && d_pi.isNull())
  {
    mkPi();
    getCurrentPiBounds(lemmas);
  }

  filterLemmas(lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size()
                    << " new lemmas during registration." << std::endl;
    return lems.size();
  }

  // process SINE phase shifting
  for (const Node& a : trNeedsMaster)
  {
    // should not have processed this already
    Assert(d_trMaster.find(a) == d_trMaster.end());
    Kind k = a.getKind();
    Assert(k == SINE || k == EXPONENTIAL);
    Node y =
        nm->mkSkolem("y", nm->realType(), "phase shifted trigonometric arg");
    Node new_a = nm->mkNode(k, y);
    d_trSlaves[new_a].push_back(new_a);
    d_trSlaves[new_a].push_back(a);
    d_trMaster[a] = new_a;
    d_trMaster[new_a] = new_a;
    Node lem;
    if (k == SINE)
    {
      Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a
                         << std::endl;
      Assert(!d_pi.isNull());
      Node shift = nm->mkSkolem("s", nm->integerType(), "number of shifts");
      // TODO : do not introduce shift here, instead needs model-based
      // refinement for constant shifts (cvc4-projects #1284)
      lem = nm->mkNode(
          AND,
          mkValidPhase(y, d_pi),
          nm->mkNode(
              ITE,
              mkValidPhase(a[0], d_pi),
              a[0].eqNode(y),
              a[0].eqNode(nm->mkNode(
                  PLUS,
                  y,
                  nm->mkNode(MULT, nm->mkConst(Rational(2)), shift, d_pi)))),
          new_a.eqNode(a));
    }
    else
    {
      // do both equalities to ensure that new_a becomes a preregistered term
      lem = nm->mkNode(AND, a.eqNode(new_a), a[0].eqNode(y));
    }
    // note we must do preprocess on this lemma
    Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : purify : " << lem
                          << std::endl;
    lemsPp.push_back(lem);
  }
  if (!lemsPp.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lemsPp.size()
                    << " new lemmas SINE phase shifting." << std::endl;
    return lemsPp.size();
  }
  Trace("nl-ext") << "We have " << d_ms.size() << " monomials." << std::endl;

  // register constants
  registerMonomial(d_one);
  for (unsigned j = 0; j < d_order_points.size(); j++) {
    Node c = d_order_points[j];
    d_model.computeConcreteModelValue(c);
    d_model.computeAbstractModelValue(c);
  }

  // register variables
  Trace("nl-ext-mv") << "Variables in monomials : " << std::endl;
  for (unsigned i = 0; i < d_ms_vars.size(); i++) {
    Node v = d_ms_vars[i];
    registerMonomial(v);
    d_model.computeConcreteModelValue(v);
    d_model.computeAbstractModelValue(v);
    d_model.printModelValue("nl-ext-mv", v);
  }
  if (Trace.isOn("nl-ext-mv"))
  {
    Trace("nl-ext-mv") << "Arguments of trancendental functions : "
                       << std::endl;
    for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
    {
      Kind k = tfl.first;
      if (k == SINE || k == EXPONENTIAL)
      {
        for (const Node& tf : tfl.second)
        {
          Node v = tf[0];
          d_model.computeConcreteModelValue(v);
          d_model.computeAbstractModelValue(v);
          d_model.printModelValue("nl-ext-mv", v);
        }
      }
    }
  }

  //----------------------------------- possibly split on zero
  if (options::nlExtSplitZero()) {
    Trace("nl-ext") << "Get zero split lemmas..." << std::endl;
    lemmas = checkSplitZero();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }
  }

  //-----------------------------------initial lemmas for transcendental functions
  lemmas = checkTranscendentalInitialRefine();
  filterLemmas(lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                    << std::endl;
    return lems.size();
  }

  //-----------------------------------lemmas based on sign (comparison to zero)
  lemmas = checkMonomialSign();
  filterLemmas(lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                    << std::endl;
    return lems.size();
  }

  //-----------------------------------monotonicity of transdental functions
  lemmas = checkTranscendentalMonotonic();
  filterLemmas(lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                    << std::endl;
    return lems.size();
  }

  //-----------------------------------lemmas based on magnitude of non-zero monomials
  Trace("nl-ext-proc") << "Assign order ids..." << std::endl;
  // sort by absolute values of abstract model values
  assignOrderIds(d_ms_vars, d_order_vars, false, true);

  // sort individual variable lists
  Trace("nl-ext-proc") << "Assign order var lists..." << std::endl;
  SortNlModel smv;
  smv.d_nlm = &d_model;
  smv.d_isConcrete = false;
  smv.d_isAbsolute = true;
  smv.d_reverse_order = true;
  for (unsigned j = 0; j < d_ms.size(); j++) {
    std::sort(d_m_vlist[d_ms[j]].begin(), d_m_vlist[d_ms[j]].end(), smv);
  }
  for (unsigned c = 0; c < 3; c++) {
    // c is effort level
    lemmas = checkMonomialMagnitude( c );
    unsigned nlem = lemmas.size();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size()
                      << " new lemmas (out of possible " << nlem << ")."
                      << std::endl;
      return lems.size();
    }
  }

  // sort monomials by degree
  Trace("nl-ext-proc") << "Sort monomials by degree..." << std::endl;
  SortNonlinearDegree snlad(d_m_degree);
  std::sort(d_ms.begin(), d_ms.end(), snlad);
  // all monomials
  d_mterms.insert(d_mterms.end(), d_ms_vars.begin(), d_ms_vars.end());
  d_mterms.insert(d_mterms.end(), d_ms.begin(), d_ms.end());

  //-----------------------------------inferred bounds lemmas
  //  e.g. x >= t => y*x >= y*t
  std::vector< Node > nt_lemmas;
  lemmas = checkMonomialInferBounds(nt_lemmas, assertions, false_asserts);
  // Trace("nl-ext") << "Bound lemmas : " << lemmas.size() << ", " <<
  // nt_lemmas.size() << std::endl;  prioritize lemmas that do not
  // introduce new monomials
  filterLemmas(lemmas, lems);

  if (options::nlExtTangentPlanes() && options::nlExtTangentPlanesInterleave())
  {
    lemmas = checkTangentPlanes();
    filterLemmas(lemmas, lems);
  }

  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                    << std::endl;
    return lems.size();
  }

  // from inferred bound inferences : now do ones that introduce new terms
  filterLemmas(nt_lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size()
                    << " new (monomial-introducing) lemmas." << std::endl;
    return lems.size();
  }

  //------------------------------------factoring lemmas
  //   x*y + x*z >= t => exists k. k = y + z ^ x*k >= t
  if( options::nlExtFactor() ){
    lemmas = checkFactoring(assertions, false_asserts);
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }
  }

  //------------------------------------resolution bound inferences
  //  e.g. ( y>=0 ^ s <= x*z ^ x*y <= t ) => y*s <= z*t
  if (options::nlExtResBound()) {
    lemmas = checkMonomialInferResBounds();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }
  }
  
  //------------------------------------tangent planes
  if (options::nlExtTangentPlanes() && !options::nlExtTangentPlanesInterleave())
  {
    lemmas = checkTangentPlanes();
    filterLemmas(lemmas, wlems);
  }
  if (options::nlExtTfTangentPlanes())
  {
    lemmas = checkTranscendentalTangentPlanes(lemSE);
    filterLemmas(lemmas, wlems);
  }
  Trace("nl-ext") << "  ...finished with " << wlems.size() << " waiting lemmas."
                  << std::endl;

  return 0;
}

void NonlinearExtension::check(Theory::Effort e) {
  Trace("nl-ext") << std::endl;
  Trace("nl-ext") << "NonlinearExtension::check, effort = " << e
                  << ", built model = " << d_builtModel.get() << std::endl;
  if (e == Theory::EFFORT_FULL)
  {
    d_containing.getExtTheory()->clearCache();
    d_needsLastCall = true;
    if (options::nlExtRewrites()) {
      std::vector<Node> nred;
      if (!d_containing.getExtTheory()->doInferences(0, nred)) {
        Trace("nl-ext") << "...sent no lemmas, # extf to reduce = "
                        << nred.size() << std::endl;
        if (nred.empty()) {
          d_needsLastCall = false;
        }
      } else {
        Trace("nl-ext") << "...sent lemmas." << std::endl;
      }
    }
  }
  else
  {
    // If we computed lemmas during collectModelInfo, send them now.
    if (!d_cmiLemmas.empty() || !d_cmiLemmasPp.empty())
    {
      sendLemmas(d_cmiLemmas, false, d_cmiLemmasSE);
      sendLemmas(d_cmiLemmasPp, true, d_cmiLemmasSE);
      return;
    }
    // Otherwise, we will answer SAT. The values that we approximated are
    // recorded as approximations here.
    TheoryModel* tm = d_containing.getValuation().getModel();
    for (std::pair<const Node, std::pair<Node, Node>>& a : d_approximations)
    {
      if (a.second.second.isNull())
      {
        tm->recordApproximation(a.first, a.second.first);
      }
      else
      {
        tm->recordApproximation(a.first, a.second.first, a.second.second);
      }
    }
  }
}

bool NonlinearExtension::modelBasedRefinement(
    std::vector<Node>& mlems,
    std::vector<Node>& mlemsPp,
    std::map<Node, NlLemmaSideEffect>& lemSE)
{
  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("nl-ext-mv-assert")
      << "Getting model values... check for [model-false]" << std::endl;
  // get the assertions that are false in the model
  const std::vector<Node> false_asserts = checkModelEval(assertions);

  // get the extended terms belonging to this theory
  std::vector<Node> xts;
  d_containing.getExtTheory()->getTerms(xts);

  if (Trace.isOn("nl-ext-debug"))
  {
    Trace("nl-ext-debug") << "  processing NonlinearExtension::check : "
                          << std::endl;
    Trace("nl-ext-debug") << "     " << false_asserts.size()
                          << " false assertions" << std::endl;
    Trace("nl-ext-debug") << "     " << xts.size()
                          << " extended terms: " << std::endl;
    Trace("nl-ext-debug") << "       ";
    for (unsigned j = 0; j < xts.size(); j++)
    {
      Trace("nl-ext-debug") << xts[j] << " ";
    }
    Trace("nl-ext-debug") << std::endl;
  }

  // compute whether shared terms have correct values
  unsigned num_shared_wrong_value = 0;
  std::vector<Node> shared_term_value_splits;
  // must ensure that shared terms are equal to their concrete value
  Trace("nl-ext-mv") << "Shared terms : " << std::endl;
  for (context::CDList<TNode>::const_iterator its =
           d_containing.shared_terms_begin();
       its != d_containing.shared_terms_end();
       ++its)
  {
    TNode shared_term = *its;
    // compute its value in the model, and its evaluation in the model
    Node stv0 = d_model.computeConcreteModelValue(shared_term);
    Node stv1 = d_model.computeAbstractModelValue(shared_term);
    d_model.printModelValue("nl-ext-mv", shared_term);
    if (stv0 != stv1)
    {
      num_shared_wrong_value++;
      Trace("nl-ext-mv") << "Bad shared term value : " << shared_term
                         << std::endl;
      if (shared_term != stv0)
      {
        // split on the value, this is non-terminating in general, TODO :
        // improve this
        Node eq = shared_term.eqNode(stv0);
        shared_term_value_splits.push_back(eq);
      }
      else
      {
        // this can happen for transcendental functions
        // the problem is that we cannot evaluate transcendental functions
        // (they don't have a rewriter that returns constants)
        // thus, the actual value in their model can be themselves, hence we
        // have no reference point to rule out the current model.  In this
        // case, we may set incomplete below.
      }
    }
  }
  Trace("nl-ext-debug") << "     " << num_shared_wrong_value
                        << " shared terms with wrong model value." << std::endl;
  bool needsRecheck;
  do
  {
    d_model.resetCheck();
    needsRecheck = false;
    // complete_status:
    //   1 : we may answer SAT, -1 : we may not answer SAT, 0 : unknown
    int complete_status = 1;
    // lemmas that should be sent later
    std::vector<Node> wlems;
    // We require a check either if an assertion is false or a shared term has
    // a wrong value
    if (!false_asserts.empty() || num_shared_wrong_value > 0)
    {
      complete_status = num_shared_wrong_value > 0 ? -1 : 0;
      checkLastCall(
          assertions, false_asserts, xts, mlems, mlemsPp, wlems, lemSE);
      if (!mlems.empty() || !mlemsPp.empty())
      {
        return true;
      }
    }
    Trace("nl-ext") << "Finished check with status : " << complete_status
                    << std::endl;

    // if we did not add a lemma during check and there is a chance for SAT
    if (complete_status == 0)
    {
      Trace("nl-ext")
          << "Check model based on bounds for irrational-valued functions..."
          << std::endl;
      // check the model based on simple solving of equalities and using
      // error bounds on the Taylor approximation of transcendental functions.
      std::vector<Node> lemmas;
      std::vector<Node> gs;
      if (checkModel(assertions, false_asserts, lemmas, gs))
      {
        complete_status = 1;
      }
      for (const Node& mg : gs)
      {
        Node mgr = Rewriter::rewrite(mg);
        mgr = d_containing.getValuation().ensureLiteral(mgr);
        d_containing.getOutputChannel().requirePhase(mgr, true);
        d_builtModel = true;
      }
      filterLemmas(lemmas, mlems);
      if (!mlems.empty())
      {
        return true;
      }
    }

    // if we have not concluded SAT
    if (complete_status != 1)
    {
      // flush the waiting lemmas
      if (!wlems.empty())
      {
        mlems.insert(mlems.end(), wlems.begin(), wlems.end());
        Trace("nl-ext") << "...added " << wlems.size() << " waiting lemmas."
                        << std::endl;
        return true;
      }
      // resort to splitting on shared terms with their model value
      // if we did not add any lemmas
      if (num_shared_wrong_value > 0)
      {
        complete_status = -1;
        if (!shared_term_value_splits.empty())
        {
          std::vector<Node> stvLemmas;
          for (const Node& eq : shared_term_value_splits)
          {
            Node req = Rewriter::rewrite(eq);
            Node literal = d_containing.getValuation().ensureLiteral(req);
            d_containing.getOutputChannel().requirePhase(literal, true);
            Trace("nl-ext-debug") << "Split on : " << literal << std::endl;
            Node split = literal.orNode(literal.negate());
            filterLemma(split, stvLemmas);
          }
          if (!stvLemmas.empty())
          {
            mlems.insert(mlems.end(), stvLemmas.begin(), stvLemmas.end());
            Trace("nl-ext") << "...added " << stvLemmas.size()
                            << " shared term value split lemmas." << std::endl;
            return true;
          }
        }
        else
        {
          // this can happen if we are trying to do theory combination with
          // trancendental functions
          // since their model value cannot even be computed exactly
        }
      }

      // we are incomplete
      if (options::nlExtIncPrecision() && d_model.usedApproximate())
      {
        d_taylor_degree++;
        needsRecheck = true;
        // increase precision for PI?
        // Difficult since Taylor series is very slow to converge
        Trace("nl-ext") << "...increment Taylor degree to " << d_taylor_degree
                        << std::endl;
      }
      else
      {
        Trace("nl-ext") << "...failed to send lemma in "
                           "NonLinearExtension, set incomplete"
                        << std::endl;
        d_containing.getOutputChannel().setIncomplete();
      }
    }
  } while (needsRecheck);

  // did not add lemmas
  return false;
}

void NonlinearExtension::interceptModel(std::map<Node, Node>& arithModel)
{
  if (!needsCheckLastEffort())
  {
    // no non-linear constraints, we are done
    return;
  }
  Trace("nl-ext") << "NonlinearExtension::interceptModel begin" << std::endl;
  d_model.reset(d_containing.getValuation().getModel(), arithModel);
  // run a last call effort check
  d_cmiLemmas.clear();
  d_cmiLemmasPp.clear();
  d_cmiLemmasSE.clear();
  if (!d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model-based refinement" << std::endl;
    modelBasedRefinement(d_cmiLemmas, d_cmiLemmasPp, d_cmiLemmasSE);
  }
  if (d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model repair" << std::endl;
    d_approximations.clear();
    // modify the model values
    d_model.getModelValueRepair(arithModel, d_approximations);
  }
}

void NonlinearExtension::presolve()
{
  Trace("nl-ext") << "NonlinearExtension::presolve" << std::endl;
}

void NonlinearExtension::assignOrderIds(std::vector<Node>& vars,
                                        NodeMultiset& order,
                                        bool isConcrete,
                                        bool isAbsolute)
{
  SortNlModel smv;
  smv.d_nlm = &d_model;
  smv.d_isConcrete = isConcrete;
  smv.d_isAbsolute = isAbsolute;
  smv.d_reverse_order = false;
  std::sort(vars.begin(), vars.end(), smv);

  order.clear();
  // assign ordering id's
  unsigned counter = 0;
  unsigned order_index = isConcrete ? 0 : 1;
  Node prev;
  for (unsigned j = 0; j < vars.size(); j++) {
    Node x = vars[j];
    Node v = d_model.computeModelValue(x, isConcrete);
    if( !v.isConst() ){
      Trace("nl-ext-mvo") << "..do not assign order to " << x << " : " << v << std::endl;
      //don't assign for non-constant values (transcendental function apps)
      break;
    }
    Trace("nl-ext-mvo") << "  order " << x << " : " << v << std::endl;
    if (v != prev) {
      // builtin points
      bool success;
      do {
        success = false;
        if (order_index < d_order_points.size()) {
          Node vv = d_model.computeModelValue(d_order_points[order_index],
                                              isConcrete);
          if (d_model.compareValue(v, vv, isAbsolute) <= 0)
          {
            counter++;
            Trace("nl-ext-mvo") << "O[" << d_order_points[order_index]
                                << "] = " << counter << std::endl;
            order[d_order_points[order_index]] = counter;
            prev = vv;
            order_index++;
            success = true;
          }
        }
      } while (success);
    }
    if (prev.isNull() || d_model.compareValue(v, prev, isAbsolute) != 0)
    {
      counter++;
    }
    Trace("nl-ext-mvo") << "O[" << x << "] = " << counter << std::endl;
    order[x] = counter;
    prev = v;
  }
  while (order_index < d_order_points.size()) {
    counter++;
    Trace("nl-ext-mvo") << "O[" << d_order_points[order_index]
                        << "] = " << counter << std::endl;
    order[d_order_points[order_index]] = counter;
    order_index++;
  }
}

void NonlinearExtension::mkPi(){
  if( d_pi.isNull() ){
    d_pi = NodeManager::currentNM()->mkNullaryOperator(
        NodeManager::currentNM()->realType(), PI);
    d_pi_2 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
        MULT,
        d_pi,
        NodeManager::currentNM()->mkConst(Rational(1) / Rational(2))));
    d_pi_neg_2 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
        MULT,
        d_pi,
        NodeManager::currentNM()->mkConst(Rational(-1) / Rational(2))));
    d_pi_neg = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
        MULT, d_pi, NodeManager::currentNM()->mkConst(Rational(-1))));
    //initialize bounds
    d_pi_bound[0] =
        NodeManager::currentNM()->mkConst(Rational(103993) / Rational(33102));
    d_pi_bound[1] =
        NodeManager::currentNM()->mkConst(Rational(104348) / Rational(33215));
  }
}

void NonlinearExtension::getCurrentPiBounds( std::vector< Node >& lemmas ) {
  Node pi_lem = NodeManager::currentNM()->mkNode(
      AND,
      NodeManager::currentNM()->mkNode(GEQ, d_pi, d_pi_bound[0]),
      NodeManager::currentNM()->mkNode(LEQ, d_pi, d_pi_bound[1]));
  lemmas.push_back( pi_lem );
}

bool NonlinearExtension::getApproximateSqrt(Node c,
                                            Node& l,
                                            Node& u,
                                            unsigned iter) const
{
  Assert(c.isConst());
  if (c == d_one || c == d_zero)
  {
    l = c;
    u = c;
    return true;
  }
  Rational rc = c.getConst<Rational>();

  Rational rl = rc < Rational(1) ? rc : Rational(1);
  Rational ru = rc < Rational(1) ? Rational(1) : rc;
  unsigned count = 0;
  Rational half = Rational(1) / Rational(2);
  while (count < iter)
  {
    Rational curr = half * (rl + ru);
    Rational curr_sq = curr * curr;
    if (curr_sq == rc)
    {
      rl = curr_sq;
      ru = curr_sq;
      break;
    }
    else if (curr_sq < rc)
    {
      rl = curr;
    }
    else
    {
      ru = curr;
    }
    count++;
  }

  NodeManager* nm = NodeManager::currentNM();
  l = nm->mkConst(rl);
  u = nm->mkConst(ru);
  return true;
}

// show a <> 0 by inequalities between variables in monomial a w.r.t 0
int NonlinearExtension::compareSign(Node oa, Node a, unsigned a_index,
                                    int status, std::vector<Node>& exp,
                                    std::vector<Node>& lem) {
  Trace("nl-ext-debug") << "Process " << a << " at index " << a_index
                        << ", status is " << status << std::endl;
  Node mvaoa = d_model.computeAbstractModelValue(oa);
  if (a_index == d_m_vlist[a].size()) {
    if (mvaoa.getConst<Rational>().sgn() != status)
    {
      Node lemma =
          safeConstructNary(AND, exp).impNode(mkLit(oa, d_zero, status * 2));
      lem.push_back(lemma);
    }
    return status;
  } else {
    Assert(a_index < d_m_vlist[a].size());
    Node av = d_m_vlist[a][a_index];
    unsigned aexp = d_m_exp[a][av];
    // take current sign in model
    Node mvaav = d_model.computeAbstractModelValue(av);
    int sgn = mvaav.getConst<Rational>().sgn();
    Trace("nl-ext-debug") << "Process var " << av << "^" << aexp
                          << ", model sign = " << sgn << std::endl;
    if (sgn == 0) {
      if (mvaoa.getConst<Rational>().sgn() != 0)
      {
        Node lemma = av.eqNode(d_zero).impNode(oa.eqNode(d_zero));
        lem.push_back(lemma);
      }
      return 0;
    } else {
      if (aexp % 2 == 0) {
        exp.push_back(av.eqNode(d_zero).negate());
        return compareSign(oa, a, a_index + 1, status, exp, lem);
      } else {
        exp.push_back(
            NodeManager::currentNM()->mkNode(sgn == 1 ? GT : LT, av, d_zero));
        return compareSign(oa, a, a_index + 1, status * sgn, exp, lem);
      }
    }
  }
}

bool NonlinearExtension::compareMonomial(
    Node oa, Node a, NodeMultiset& a_exp_proc, Node ob, Node b,
    NodeMultiset& b_exp_proc, std::vector<Node>& exp, std::vector<Node>& lem,
    std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers) {
  Trace("nl-ext-comp-debug")
      << "Check |" << a << "| >= |" << b << "|" << std::endl;
  unsigned pexp_size = exp.size();
  if (compareMonomial(oa, a, 0, a_exp_proc, ob, b, 0, b_exp_proc, 0, exp, lem,
                      cmp_infers)) {
    return true;
  } else {
    exp.resize(pexp_size);
    Trace("nl-ext-comp-debug")
        << "Check |" << b << "| >= |" << a << "|" << std::endl;
    if (compareMonomial(ob, b, 0, b_exp_proc, oa, a, 0, a_exp_proc, 0, exp, lem,
                        cmp_infers)) {
      return true;
    } else {
      return false;
    }
  }
}

bool NonlinearExtension::cmp_holds(
    Node x, Node y, std::map<Node, std::map<Node, Node> >& cmp_infers,
    std::vector<Node>& exp, std::map<Node, bool>& visited) {
  if (x == y) {
    return true;
  } else if (visited.find(x) == visited.end()) {
    visited[x] = true;
    std::map<Node, std::map<Node, Node> >::iterator it = cmp_infers.find(x);
    if (it != cmp_infers.end()) {
      for (std::map<Node, Node>::iterator itc = it->second.begin();
           itc != it->second.end(); ++itc) {
        exp.push_back(itc->second);
        if (cmp_holds(itc->first, y, cmp_infers, exp, visited)) {
          return true;
        }
        exp.pop_back();
      }
    }
  }
  return false;
}

// trying to show a ( >, = ) b   by inequalities between variables in
// monomials a,b
bool NonlinearExtension::compareMonomial(
    Node oa, Node a, unsigned a_index, NodeMultiset& a_exp_proc, Node ob,
    Node b, unsigned b_index, NodeMultiset& b_exp_proc, int status,
    std::vector<Node>& exp, std::vector<Node>& lem,
    std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers) {
  Trace("nl-ext-comp-debug")
      << "compareMonomial " << oa << " and " << ob << ", indices = " << a_index
      << " " << b_index << std::endl;
  Assert(status == 0 || status == 2);
  if (a_index == d_m_vlist[a].size() && b_index == d_m_vlist[b].size()) {
    // finished, compare absolute value of abstract model values
    int modelStatus = d_model.compare(oa, ob, false, true) * -2;
    Trace("nl-ext-comp") << "...finished comparison with " << oa << " <"
                         << status << "> " << ob
                         << ", model status = " << modelStatus << std::endl;
    if (status != modelStatus) {
      Trace("nl-ext-comp-infer")
          << "infer : " << oa << " <" << status << "> " << ob << std::endl;
      if (status == 2) {
        // must state that all variables are non-zero
        for (unsigned j = 0; j < d_m_vlist[a].size(); j++) {
          exp.push_back(d_m_vlist[a][j].eqNode(d_zero).negate());
        }
      }
      Node clem = NodeManager::currentNM()->mkNode(
          IMPLIES, safeConstructNary(AND, exp), mkLit(oa, ob, status, true));
      Trace("nl-ext-comp-lemma") << "comparison lemma : " << clem << std::endl;
      lem.push_back(clem);
      cmp_infers[status][oa][ob] = clem;
    }
    return true;
  } else {
    // get a/b variable information
    Node av;
    unsigned aexp = 0;
    unsigned avo = 0;
    if (a_index < d_m_vlist[a].size()) {
      av = d_m_vlist[a][a_index];
      Assert(a_exp_proc[av] <= d_m_exp[a][av]);
      aexp = d_m_exp[a][av] - a_exp_proc[av];
      if (aexp == 0) {
        return compareMonomial(oa, a, a_index + 1, a_exp_proc, ob, b, b_index,
                               b_exp_proc, status, exp, lem, cmp_infers);
      }
      Assert(d_order_vars.find(av) != d_order_vars.end());
      avo = d_order_vars[av];
    }
    Node bv;
    unsigned bexp = 0;
    unsigned bvo = 0;
    if (b_index < d_m_vlist[b].size()) {
      bv = d_m_vlist[b][b_index];
      Assert(b_exp_proc[bv] <= d_m_exp[b][bv]);
      bexp = d_m_exp[b][bv] - b_exp_proc[bv];
      if (bexp == 0) {
        return compareMonomial(oa, a, a_index, a_exp_proc, ob, b, b_index + 1,
                               b_exp_proc, status, exp, lem, cmp_infers);
      }
      Assert(d_order_vars.find(bv) != d_order_vars.end());
      bvo = d_order_vars[bv];
    }
    // get "one" information
    Assert(d_order_vars.find(d_one) != d_order_vars.end());
    unsigned ovo = d_order_vars[d_one];
    Trace("nl-ext-comp-debug") << "....vars : " << av << "^" << aexp << " "
                               << bv << "^" << bexp << std::endl;

    //--- cases
    if (av.isNull()) {
      if (bvo <= ovo) {
        Trace("nl-ext-comp-debug") << "...take leading " << bv << std::endl;
        // can multiply b by <=1
        exp.push_back(mkLit(d_one, bv, bvo == ovo ? 0 : 2, true));
        return compareMonomial(oa, a, a_index, a_exp_proc, ob, b, b_index + 1,
                               b_exp_proc, bvo == ovo ? status : 2, exp, lem,
                               cmp_infers);
      } else {
        Trace("nl-ext-comp-debug")
            << "...failure, unmatched |b|>1 component." << std::endl;
        return false;
      }
    } else if (bv.isNull()) {
      if (avo >= ovo) {
        Trace("nl-ext-comp-debug") << "...take leading " << av << std::endl;
        // can multiply a by >=1
        exp.push_back(mkLit(av, d_one, avo == ovo ? 0 : 2, true));
        return compareMonomial(oa, a, a_index + 1, a_exp_proc, ob, b, b_index,
                               b_exp_proc, avo == ovo ? status : 2, exp, lem,
                               cmp_infers);
      } else {
        Trace("nl-ext-comp-debug")
            << "...failure, unmatched |a|<1 component." << std::endl;
        return false;
      }
    } else {
      Assert(!av.isNull() && !bv.isNull());
      if (avo >= bvo) {
        if (bvo < ovo && avo >= ovo) {
          Trace("nl-ext-comp-debug") << "...take leading " << av << std::endl;
          // do avo>=1 instead
          exp.push_back(mkLit(av, d_one, avo == ovo ? 0 : 2, true));
          return compareMonomial(oa, a, a_index + 1, a_exp_proc, ob, b, b_index,
                                 b_exp_proc, avo == ovo ? status : 2, exp, lem,
                                 cmp_infers);
        } else {
          unsigned min_exp = aexp > bexp ? bexp : aexp;
          a_exp_proc[av] += min_exp;
          b_exp_proc[bv] += min_exp;
          Trace("nl-ext-comp-debug")
              << "...take leading " << min_exp << " from " << av << " and "
              << bv << std::endl;
          exp.push_back(mkLit(av, bv, avo == bvo ? 0 : 2, true));
          bool ret = compareMonomial(oa, a, a_index, a_exp_proc, ob, b, b_index,
                                     b_exp_proc, avo == bvo ? status : 2, exp,
                                     lem, cmp_infers);
          a_exp_proc[av] -= min_exp;
          b_exp_proc[bv] -= min_exp;
          return ret;
        }
      } else {
        if (bvo <= ovo) {
          Trace("nl-ext-comp-debug") << "...take leading " << bv << std::endl;
          // try multiply b <= 1
          exp.push_back(mkLit(d_one, bv, bvo == ovo ? 0 : 2, true));
          return compareMonomial(oa, a, a_index, a_exp_proc, ob, b, b_index + 1,
                                 b_exp_proc, bvo == ovo ? status : 2, exp, lem,
                                 cmp_infers);
        } else {
          Trace("nl-ext-comp-debug")
              << "...failure, leading |b|>|a|>1 component." << std::endl;
          return false;
        }
      }
    }
  }
}

// status 0 : n equal, -1 : n superset, 1 : n subset
void NonlinearExtension::MonomialIndex::addTerm(Node n,
                                                const std::vector<Node>& reps,
                                                NonlinearExtension* nla,
                                                int status, unsigned argIndex) {
  if (status == 0) {
    if (argIndex == reps.size()) {
      d_monos.push_back(n);
    } else {
      d_data[reps[argIndex]].addTerm(n, reps, nla, status, argIndex + 1);
    }
  }
  for (std::map<Node, MonomialIndex>::iterator it = d_data.begin();
       it != d_data.end(); ++it) {
    if (status != 0 || argIndex == reps.size() || it->first != reps[argIndex]) {
      // if we do not contain this variable, then if we were a superset,
      // fail (-2), otherwise we are subset.  if we do contain this
      // variable, then if we were equal, we are superset since variables
      // are ordered, otherwise we remain the same.
      int new_status =
          std::find(reps.begin(), reps.end(), it->first) == reps.end()
              ? (status >= 0 ? 1 : -2)
              : (status == 0 ? -1 : status);
      if (new_status != -2) {
        it->second.addTerm(n, reps, nla, new_status, argIndex);
      }
    }
  }
  // compare for subsets
  for (unsigned i = 0; i < d_monos.size(); i++) {
    Node m = d_monos[i];
    if (m != n) {
      // we are superset if we are equal and haven't traversed all variables
      int cstatus = status == 0 ? (argIndex == reps.size() ? 0 : -1) : status;
      Trace("nl-ext-mindex-debug") << "  compare " << n << " and " << m
                                   << ", status = " << cstatus << std::endl;
      if (cstatus <= 0 && nla->isMonomialSubset(m, n)) {
        nla->registerMonomialSubset(m, n);
        Trace("nl-ext-mindex-debug") << "...success" << std::endl;
      } else if (cstatus >= 0 && nla->isMonomialSubset(n, m)) {
        nla->registerMonomialSubset(n, m);
        Trace("nl-ext-mindex-debug") << "...success (rev)" << std::endl;
      }
    }
  }
}

std::vector<Node> NonlinearExtension::checkMonomialSign() {
  std::vector<Node> lemmas;
  std::map<Node, int> signs;
  Trace("nl-ext") << "Get monomial sign lemmas..." << std::endl;
  for (unsigned j = 0; j < d_ms.size(); j++) {
    Node a = d_ms[j];
    if (d_ms_proc.find(a) == d_ms_proc.end()) {
      std::vector<Node> exp;
      if (Trace.isOn("nl-ext-debug"))
      {
        Node cmva = d_model.computeConcreteModelValue(a);
        Trace("nl-ext-debug")
            << "  process " << a << ", mv=" << cmva << "..." << std::endl;
      }
      if( d_m_nconst_factor.find( a )==d_m_nconst_factor.end() ){
        signs[a] = compareSign(a, a, 0, 1, exp, lemmas);
        if (signs[a] == 0) {
          d_ms_proc[a] = true;
          Trace("nl-ext-debug") << "...mark " << a
                             << " reduced since its value is 0." << std::endl;
        }
      }else{
        Trace("nl-ext-debug") << "...can't conclude sign lemma for " << a << " since model value of a factor is non-constant." << std::endl;
        //TODO
      }
    }
  }
  return lemmas;
}

std::vector<Node> NonlinearExtension::checkMonomialMagnitude( unsigned c ) {
  unsigned r = 1;
  std::vector<Node> lemmas;
// if (x,y,L) in cmp_infers, then x > y inferred as conclusion of L
  // in lemmas
  std::map<int, std::map<Node, std::map<Node, Node> > > cmp_infers;
  Trace("nl-ext") << "Get monomial comparison lemmas (order=" << r
                  << ", compare=" << c << ")..." << std::endl;
  for (unsigned j = 0; j < d_ms.size(); j++) {
    Node a = d_ms[j];
    if (d_ms_proc.find(a) == d_ms_proc.end() && 
        d_m_nconst_factor.find( a )==d_m_nconst_factor.end()) {
      if (c == 0) {
        // compare magnitude against 1
        std::vector<Node> exp;
        NodeMultiset a_exp_proc;
        NodeMultiset b_exp_proc;
        compareMonomial(a, a, a_exp_proc, d_one, d_one, b_exp_proc, exp,
                        lemmas, cmp_infers);
      } else {
        std::map<Node, NodeMultiset>::iterator itmea = d_m_exp.find(a);
        Assert(itmea != d_m_exp.end());
        if (c == 1) {
          // TODO : not just against containing variables?
          // compare magnitude against variables
          for (unsigned k = 0; k < d_ms_vars.size(); k++) {
            Node v = d_ms_vars[k];
            Node mvcv = d_model.computeConcreteModelValue(v);
            if (mvcv.isConst())
            {
              std::vector<Node> exp;
              NodeMultiset a_exp_proc;
              NodeMultiset b_exp_proc;
              if (itmea->second.find(v) != itmea->second.end()) {
                a_exp_proc[v] = 1;
                b_exp_proc[v] = 1;
                setMonomialFactor(a, v, a_exp_proc);
                setMonomialFactor(v, a, b_exp_proc);
                compareMonomial(a, a, a_exp_proc, v, v, b_exp_proc, exp,
                                lemmas, cmp_infers);
              }
            }
          }
        } else {
          // compare magnitude against other non-linear monomials
          for (unsigned k = (j + 1); k < d_ms.size(); k++) {
            Node b = d_ms[k];
            //(signs[a]==signs[b])==(r==0)
            if (d_ms_proc.find(b) == d_ms_proc.end() && 
                d_m_nconst_factor.find( b )==d_m_nconst_factor.end()) {
              std::map<Node, NodeMultiset>::iterator itmeb =
                  d_m_exp.find(b);
              Assert(itmeb != d_m_exp.end());

              std::vector<Node> exp;
              // take common factors of monomials, set minimum of
              // common exponents as processed
              NodeMultiset a_exp_proc;
              NodeMultiset b_exp_proc;
              for (NodeMultiset::iterator itmea2 = itmea->second.begin();
                   itmea2 != itmea->second.end(); ++itmea2) {
                NodeMultiset::iterator itmeb2 =
                    itmeb->second.find(itmea2->first);
                if (itmeb2 != itmeb->second.end()) {
                  unsigned min_exp = itmea2->second > itmeb2->second
                                         ? itmeb2->second
                                         : itmea2->second;
                  a_exp_proc[itmea2->first] = min_exp;
                  b_exp_proc[itmea2->first] = min_exp;
                  Trace("nl-ext-comp")
                      << "Common exponent : " << itmea2->first << " : "
                      << min_exp << std::endl;
                }
              }
              if (!a_exp_proc.empty()) {
                setMonomialFactor(a, b, a_exp_proc);
                setMonomialFactor(b, a, b_exp_proc);
              }
              /*
              if( !a_exp_proc.empty() ){
                //reduction based on common exponents a > 0 => ( a * b
              <> a * c <=> b <> c ), a < 0 => ( a * b <> a * c <=> b
              !<> c )  ? }else{ compareMonomial( a, a, a_exp_proc, b,
              b, b_exp_proc, exp, lemmas );
              }
              */
              compareMonomial(a, a, a_exp_proc, b, b, b_exp_proc, exp,
                              lemmas, cmp_infers);
            }
          }
        }
      }
    }
  }
  // remove redundant lemmas, e.g. if a > b, b > c, a > c were
  // inferred, discard lemma with conclusion a > c
  Trace("nl-ext-comp") << "Compute redundancies for " << lemmas.size()
                       << " lemmas." << std::endl;
  // naive
  std::vector<Node> r_lemmas;
  for (std::map<int, std::map<Node, std::map<Node, Node> > >::iterator itb =
           cmp_infers.begin();
       itb != cmp_infers.end(); ++itb) {
    for (std::map<Node, std::map<Node, Node> >::iterator itc =
             itb->second.begin();
         itc != itb->second.end(); ++itc) {
      for (std::map<Node, Node>::iterator itc2 = itc->second.begin();
           itc2 != itc->second.end(); ++itc2) {
        std::map<Node, bool> visited;
        for (std::map<Node, Node>::iterator itc3 = itc->second.begin();
             itc3 != itc->second.end(); ++itc3) {
          if (itc3->first != itc2->first) {
            std::vector<Node> exp;
            if (cmp_holds(itc3->first, itc2->first, itb->second, exp,
                          visited)) {
              r_lemmas.push_back(itc2->second);
              Trace("nl-ext-comp")
                  << "...inference of " << itc->first << " > "
                  << itc2->first << " was redundant." << std::endl;
              break;
            }
          }
        }
      }
    }
  }
  std::vector<Node> nr_lemmas;
  for (unsigned i = 0; i < lemmas.size(); i++) {
    if (std::find(r_lemmas.begin(), r_lemmas.end(), lemmas[i]) ==
        r_lemmas.end()) {
      nr_lemmas.push_back(lemmas[i]);
    }
  }
  // TODO: only take maximal lower/minimial lower bounds?

  Trace("nl-ext-comp") << nr_lemmas.size() << " / " << lemmas.size()
                       << " were non-redundant." << std::endl;
  return nr_lemmas;
}

std::vector<Node> NonlinearExtension::checkTangentPlanes() {
  std::vector< Node > lemmas;
  Trace("nl-ext") << "Get monomial tangent plane lemmas..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  unsigned kstart = d_ms_vars.size();
  for (unsigned k = kstart; k < d_mterms.size(); k++) {
    Node t = d_mterms[k];
    // if this term requires a refinement
    if (d_tplane_refine.find(t) != d_tplane_refine.end())
    {
      Trace("nl-ext-tplanes")
          << "Look at monomial requiring refinement : " << t << std::endl;
      // get a decomposition
      std::map<Node, std::vector<Node> >::iterator it =
          d_m_contain_children.find(t);
      if (it != d_m_contain_children.end()) {
        std::map<Node, std::map<Node, bool> > dproc;
        for (unsigned j = 0; j < it->second.size(); j++) {
          Node tc = it->second[j];
          if (tc != d_one) {
            Node tc_diff = d_m_contain_umult[tc][t];
            Assert(!tc_diff.isNull());
            Node a = tc < tc_diff ? tc : tc_diff;
            Node b = tc < tc_diff ? tc_diff : tc;
            if (dproc[a].find(b) == dproc[a].end()) {
              dproc[a][b] = true;
              Trace("nl-ext-tplanes")
                  << "  decomposable into : " << a << " * " << b << std::endl;
              Node a_v_c = d_model.computeAbstractModelValue(a);
              Node b_v_c = d_model.computeAbstractModelValue(b);
              // points we will add tangent planes for
              std::vector< Node > pts[2];
              pts[0].push_back( a_v_c );
              pts[1].push_back( b_v_c );
              // if previously refined
              bool prevRefine = d_tangent_val_bound[0][a].find( b )!=d_tangent_val_bound[0][a].end();
              // a_min, a_max, b_min, b_max
              for( unsigned p=0; p<4; p++ ){
                Node curr_v = p<=1 ? a_v_c : b_v_c;
                if( prevRefine ){
                  Node pt_v = d_tangent_val_bound[p][a][b];
                  Assert(!pt_v.isNull());
                  if( curr_v!=pt_v ){
                    Node do_extend =
                        nm->mkNode((p == 1 || p == 3) ? GT : LT, curr_v, pt_v);
                    do_extend = Rewriter::rewrite( do_extend );
                    if( do_extend==d_true ){
                      for( unsigned q=0; q<2; q++ ){
                        pts[ p<=1 ? 0 : 1 ].push_back( curr_v );
                        pts[ p<=1 ? 1 : 0 ].push_back( d_tangent_val_bound[ p<=1 ? 2+q : q ][a][b] );
                      }
                    }
                  }
                }else{
                  d_tangent_val_bound[p][a][b] = curr_v;
                }
              }
              
              for( unsigned p=0; p<pts[0].size(); p++ ){
                Node a_v = pts[0][p];
                Node b_v = pts[1][p];
              
                // tangent plane
                Node tplane = nm->mkNode(MINUS,
                                         nm->mkNode(PLUS,
                                                    nm->mkNode(MULT, b_v, a),
                                                    nm->mkNode(MULT, a_v, b)),
                                         nm->mkNode(MULT, a_v, b_v));
                for (unsigned d = 0; d < 4; d++) {
                  Node aa = nm->mkNode(d == 0 || d == 3 ? GEQ : LEQ, a, a_v);
                  Node ab = nm->mkNode(d == 1 || d == 3 ? GEQ : LEQ, b, b_v);
                  Node conc = nm->mkNode(d <= 1 ? LEQ : GEQ, t, tplane);
                  Node tlem = nm->mkNode(OR, aa.negate(), ab.negate(), conc);
                  Trace("nl-ext-tplanes")
                      << "Tangent plane lemma : " << tlem << std::endl;
                  lemmas.push_back(tlem);
                }

                // tangent plane reverse implication

                // t <= tplane -> ( (a <= a_v ^ b >= b_v) v
                // (a >= a_v ^ b <= b_v) ).
                // in clause form, the above becomes
                // t <= tplane -> a <= a_v v b <= b_v.
                // t <= tplane -> b >= b_v v a >= a_v.
                Node a_leq_av = nm->mkNode(LEQ, a, a_v);
                Node b_leq_bv = nm->mkNode(LEQ, b, b_v);
                Node a_geq_av = nm->mkNode(GEQ, a, a_v);
                Node b_geq_bv = nm->mkNode(GEQ, b, b_v);

                Node t_leq_tplane = nm->mkNode(LEQ, t, tplane);
                Node a_leq_av_or_b_leq_bv = nm->mkNode(OR, a_leq_av, b_leq_bv);
                Node b_geq_bv_or_a_geq_av = nm->mkNode(OR, b_geq_bv, a_geq_av);
                Node ub_reverse1 =
                    nm->mkNode(OR, t_leq_tplane.negate(), a_leq_av_or_b_leq_bv);
                Trace("nl-ext-tplanes")
                    << "Tangent plane lemma (reverse) : " << ub_reverse1
                    << std::endl;
                lemmas.push_back(ub_reverse1);
                Node ub_reverse2 =
                    nm->mkNode(OR, t_leq_tplane.negate(), b_geq_bv_or_a_geq_av);
                Trace("nl-ext-tplanes")
                    << "Tangent plane lemma (reverse) : " << ub_reverse2
                    << std::endl;
                lemmas.push_back(ub_reverse2);

                // t >= tplane -> ( (a <= a_v ^ b <= b_v) v
                // (a >= a_v ^ b >= b_v) ).
                // in clause form, the above becomes
                // t >= tplane -> a <= a_v v b >= b_v.
                // t >= tplane -> b >= b_v v a <= a_v
                Node t_geq_tplane = nm->mkNode(GEQ, t, tplane);
                Node a_leq_av_or_b_geq_bv = nm->mkNode(OR, a_leq_av, b_geq_bv);
                Node a_geq_av_or_b_leq_bv = nm->mkNode(OR, a_geq_av, b_leq_bv);
                Node lb_reverse1 =
                    nm->mkNode(OR, t_geq_tplane.negate(), a_leq_av_or_b_geq_bv);
                Trace("nl-ext-tplanes")
                    << "Tangent plane lemma (reverse) : " << lb_reverse1
                    << std::endl;
                lemmas.push_back(lb_reverse1);
                Node lb_reverse2 =
                    nm->mkNode(OR, t_geq_tplane.negate(), a_geq_av_or_b_leq_bv);
                Trace("nl-ext-tplanes")
                    << "Tangent plane lemma (reverse) : " << lb_reverse2
                    << std::endl;
                lemmas.push_back(lb_reverse2);
              }
            }
          }
        }
      }
    }
  }
  Trace("nl-ext") << "...trying " << lemmas.size()
                  << " tangent plane lemmas..." << std::endl;
  return lemmas;
}

std::vector<Node> NonlinearExtension::checkMonomialInferBounds(
    std::vector<Node>& nt_lemmas,
    const std::vector<Node>& asserts,
    const std::vector<Node>& false_asserts)
{
  std::vector< Node > lemmas; 
  // register constraints
  Trace("nl-ext-debug") << "Register bound constraints..." << std::endl;
  for (const Node& lit : asserts)
  {
    bool polarity = lit.getKind() != NOT;
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    registerConstraint(atom);
    bool is_false_lit =
        std::find(false_asserts.begin(), false_asserts.end(), lit)
        != false_asserts.end();
    // add information about bounds to variables
    std::map<Node, std::map<Node, ConstraintInfo> >::iterator itc =
        d_c_info.find(atom);
    std::map<Node, std::map<Node, bool> >::iterator itcm =
        d_c_info_maxm.find(atom);
    if (itc != d_c_info.end()) {
      Assert(itcm != d_c_info_maxm.end());
      for (std::map<Node, ConstraintInfo>::iterator itcc = itc->second.begin();
           itcc != itc->second.end(); ++itcc) {
        Node x = itcc->first;
        Node coeff = itcc->second.d_coeff;
        Node rhs = itcc->second.d_rhs;
        Kind type = itcc->second.d_type;
        Node exp = lit;
        if (!polarity) {
          // reverse
          if (type == EQUAL)
          {
            // we will take the strict inequality in the direction of the
            // model
            Node lhs = ArithMSum::mkCoeffTerm(coeff, x);
            Node query = NodeManager::currentNM()->mkNode(GT, lhs, rhs);
            Node query_mv = d_model.computeAbstractModelValue(query);
            if (query_mv == d_true) {
              exp = query;
              type = GT;
            } else {
              Assert(query_mv == d_false);
              exp = NodeManager::currentNM()->mkNode(LT, lhs, rhs);
              type = LT;
            }
          } else {
            type = negateKind(type);
          }
        }
        // add to status if maximal degree
        d_ci_max[x][coeff][rhs] = itcm->second.find(x) != itcm->second.end();
        if (Trace.isOn("nl-ext-bound-debug2")) {
          Node t = ArithMSum::mkCoeffTerm(coeff, x);
          Trace("nl-ext-bound-debug2")
              << "Add Bound: " << t << " " << type << " " << rhs << " by "
              << exp << std::endl;
        }
        bool updated = true;
        std::map<Node, Kind>::iterator its = d_ci[x][coeff].find(rhs);
        if (its == d_ci[x][coeff].end()) {
          d_ci[x][coeff][rhs] = type;
          d_ci_exp[x][coeff][rhs] = exp;
        } else if (type != its->second) {
          Trace("nl-ext-bound-debug2")
              << "Joining kinds : " << type << " " << its->second << std::endl;
          Kind jk = joinKinds(type, its->second);
          if (jk == UNDEFINED_KIND)
          {
            updated = false;
          } else if (jk != its->second) {
            if (jk == type) {
              d_ci[x][coeff][rhs] = type;
              d_ci_exp[x][coeff][rhs] = exp;
            } else {
              d_ci[x][coeff][rhs] = jk;
              d_ci_exp[x][coeff][rhs] = NodeManager::currentNM()->mkNode(
                  AND, d_ci_exp[x][coeff][rhs], exp);
            }
          } else {
            updated = false;
          }
        }
        if (Trace.isOn("nl-ext-bound")) {
          if (updated) {
            Trace("nl-ext-bound") << "Bound: ";
            debugPrintBound("nl-ext-bound", coeff, x, d_ci[x][coeff][rhs], rhs);
            Trace("nl-ext-bound") << " by " << d_ci_exp[x][coeff][rhs];
            if (d_ci_max[x][coeff][rhs]) {
              Trace("nl-ext-bound") << ", is max degree";
            }
            Trace("nl-ext-bound") << std::endl;
          }
        }
        // compute if bound is not satisfied, and store what is required
        // for a possible refinement
        if (options::nlExtTangentPlanes()) {
          if (is_false_lit) {
            d_tplane_refine.insert(x);
          }
        }
      }
    }
  }
  // reflexive constraints
  Node null_coeff;
  for (unsigned j = 0; j < d_mterms.size(); j++) {
    Node n = d_mterms[j];
    d_ci[n][null_coeff][n] = EQUAL;
    d_ci_exp[n][null_coeff][n] = d_true;
    d_ci_max[n][null_coeff][n] = false;
  }

  Trace("nl-ext") << "Get inferred bound lemmas..." << std::endl;
  
  for (unsigned k = 0; k < d_mterms.size(); k++) {
    Node x = d_mterms[k];
    Trace("nl-ext-bound-debug")
        << "Process bounds for " << x << " : " << std::endl;
    std::map<Node, std::vector<Node> >::iterator itm =
        d_m_contain_parent.find(x);
    if (itm != d_m_contain_parent.end()) {
      Trace("nl-ext-bound-debug") << "...has " << itm->second.size()
                                  << " parent monomials." << std::endl;
      // check derived bounds
      std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itc =
          d_ci.find(x);
      if (itc != d_ci.end()) {
        for (std::map<Node, std::map<Node, Kind> >::iterator itcc =
                 itc->second.begin();
             itcc != itc->second.end(); ++itcc) {
          Node coeff = itcc->first;
          Node t = ArithMSum::mkCoeffTerm(coeff, x);
          for (std::map<Node, Kind>::iterator itcr = itcc->second.begin();
               itcr != itcc->second.end(); ++itcr) {
            Node rhs = itcr->first;
            // only consider this bound if maximal degree
            if (d_ci_max[x][coeff][rhs]) {
              Kind type = itcr->second;
              for (unsigned j = 0; j < itm->second.size(); j++) {
                Node y = itm->second[j];
                Assert(d_m_contain_mult[x].find(y)
                       != d_m_contain_mult[x].end());
                Node mult = d_m_contain_mult[x][y];
                // x <k> t => m*x <k'> t  where y = m*x
                // get the sign of mult
                Node mmv = d_model.computeConcreteModelValue(mult);
                Trace("nl-ext-bound-debug2")
                    << "Model value of " << mult << " is " << mmv << std::endl;
                if(mmv.isConst()){
                  int mmv_sign = mmv.getConst<Rational>().sgn();
                  Trace("nl-ext-bound-debug2")
                      << "  sign of " << mmv << " is " << mmv_sign << std::endl;
                  if (mmv_sign != 0) {
                    Trace("nl-ext-bound-debug")
                        << "  from " << x << " * " << mult << " = " << y
                        << " and " << t << " " << type << " " << rhs
                        << ", infer : " << std::endl;
                    Kind infer_type =
                        mmv_sign == -1 ? reverseRelationKind(type) : type;
                    Node infer_lhs =
                        NodeManager::currentNM()->mkNode(MULT, mult, t);
                    Node infer_rhs =
                        NodeManager::currentNM()->mkNode(MULT, mult, rhs);
                    Node infer = NodeManager::currentNM()->mkNode(
                        infer_type, infer_lhs, infer_rhs);
                    Trace("nl-ext-bound-debug") << "     " << infer << std::endl;
                    infer = Rewriter::rewrite(infer);
                    Trace("nl-ext-bound-debug2")
                        << "     ...rewritten : " << infer << std::endl;
                    // check whether it is false in model for abstraction
                    Node infer_mv = d_model.computeAbstractModelValue(infer);
                    Trace("nl-ext-bound-debug")
                        << "       ...infer model value is " << infer_mv
                        << std::endl;
                    if (infer_mv == d_false) {
                      Node exp = NodeManager::currentNM()->mkNode(
                          AND,
                          NodeManager::currentNM()->mkNode(
                              mmv_sign == 1 ? GT : LT, mult, d_zero),
                          d_ci_exp[x][coeff][rhs]);
                      Node iblem =
                          NodeManager::currentNM()->mkNode(IMPLIES, exp, infer);
                      Node pr_iblem = iblem;
                      iblem = Rewriter::rewrite(iblem);
                      bool introNewTerms = hasNewMonomials(iblem, d_ms);
                      Trace("nl-ext-bound-lemma")
                          << "*** Bound inference lemma : " << iblem
                          << " (pre-rewrite : " << pr_iblem << ")" << std::endl;
                      // Trace("nl-ext-bound-lemma") << "       intro new
                      // monomials = " << introNewTerms << std::endl;
                      if (!introNewTerms) {
                        lemmas.push_back(iblem);
                      } else {
                        nt_lemmas.push_back(iblem);
                      }
                    }
                  } else {
                    Trace("nl-ext-bound-debug") << "     ...coefficient " << mult
                                                << " is zero." << std::endl;
                  }
                }else{
                  Trace("nl-ext-bound-debug") << "     ...coefficient " << mult
                                              << " is non-constant (probably transcendental)." << std::endl;
                }
              }
            }
          }
        }
      }
    } else {
      Trace("nl-ext-bound-debug") << "...has no parent monomials." << std::endl;
    }
  }
  return lemmas;
}

std::vector<Node> NonlinearExtension::checkFactoring(
    const std::vector<Node>& asserts, const std::vector<Node>& false_asserts)
{
  std::vector< Node > lemmas; 
  Trace("nl-ext") << "Get factoring lemmas..." << std::endl;
  for (const Node& lit : asserts)
  {
    bool polarity = lit.getKind() != NOT;
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    Node litv = d_model.computeConcreteModelValue(lit);
    bool considerLit = false;
    // Only consider literals that are in false_asserts.
    considerLit = std::find(false_asserts.begin(), false_asserts.end(), lit)
                  != false_asserts.end();

    if (considerLit)
    {
      std::map<Node, Node> msum;
      if (ArithMSum::getMonomialSumLit(atom, msum))
      {
        Trace("nl-ext-factor") << "Factoring for literal " << lit << ", monomial sum is : " << std::endl;
        if (Trace.isOn("nl-ext-factor")) {
          ArithMSum::debugPrintMonomialSum(msum, "nl-ext-factor");
        }
        std::map< Node, std::vector< Node > > factor_to_mono;
        std::map< Node, std::vector< Node > > factor_to_mono_orig;
        for( std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
          if( !itm->first.isNull() ){
            if( itm->first.getKind()==NONLINEAR_MULT ){
              std::vector< Node > children;
              for( unsigned i=0; i<itm->first.getNumChildren(); i++ ){
                children.push_back( itm->first[i] );
              }
              std::map< Node, bool > processed;
              for( unsigned i=0; i<itm->first.getNumChildren(); i++ ){
                if( processed.find( itm->first[i] )==processed.end() ){
                  processed[itm->first[i]] = true;
                  children[i] = d_one;
                  if( !itm->second.isNull() ){
                    children.push_back( itm->second );
                  }
                  Node val = NodeManager::currentNM()->mkNode(MULT, children);
                  if( !itm->second.isNull() ){
                    children.pop_back();
                  }
                  children[i] = itm->first[i];
                  val = Rewriter::rewrite( val );
                  factor_to_mono[itm->first[i]].push_back( val );
                  factor_to_mono_orig[itm->first[i]].push_back( itm->first );
                }
              }
            }
          }
        }
        for( std::map< Node, std::vector< Node > >::iterator itf = factor_to_mono.begin(); itf != factor_to_mono.end(); ++itf ){
          Node x = itf->first;
          if (itf->second.size() == 1)
          {
            std::map<Node, Node>::iterator itm = msum.find(x);
            if (itm != msum.end())
            {
              itf->second.push_back(itm->second.isNull() ? d_one : itm->second);
              factor_to_mono_orig[x].push_back(x);
            }
          }
          if( itf->second.size()>1 ){
            Node sum = NodeManager::currentNM()->mkNode(PLUS, itf->second);
            sum = Rewriter::rewrite( sum );
            Trace("nl-ext-factor")
                << "* Factored sum for " << x << " : " << sum << std::endl;
            Node kf = getFactorSkolem(sum, lemmas);
            std::vector< Node > poly;
            poly.push_back(NodeManager::currentNM()->mkNode(MULT, x, kf));
            std::map<Node, std::vector<Node> >::iterator itfo =
                factor_to_mono_orig.find(x);
            Assert(itfo != factor_to_mono_orig.end());
            for( std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
              if( std::find( itfo->second.begin(), itfo->second.end(), itm->first )==itfo->second.end() ){
                poly.push_back(ArithMSum::mkCoeffTerm(
                    itm->second, itm->first.isNull() ? d_one : itm->first));
              }
            }
            Node polyn = poly.size() == 1
                             ? poly[0]
                             : NodeManager::currentNM()->mkNode(PLUS, poly);
            Trace("nl-ext-factor") << "...factored polynomial : " << polyn << std::endl;
            Node conc_lit = NodeManager::currentNM()->mkNode( atom.getKind(), polyn, d_zero );
            conc_lit = Rewriter::rewrite( conc_lit );
            if( !polarity ){
              conc_lit = conc_lit.negate();
            }
            
            std::vector< Node > lemma_disj;
            lemma_disj.push_back( lit.negate() );
            lemma_disj.push_back( conc_lit );
            Node flem = NodeManager::currentNM()->mkNode(OR, lemma_disj);
            Trace("nl-ext-factor") << "...lemma is " << flem << std::endl;
            lemmas.push_back( flem ); 
          }
        }
      }
    }
  }
  return lemmas;
}

Node NonlinearExtension::getFactorSkolem( Node n, std::vector< Node >& lemmas ) {
  std::map< Node, Node >::iterator itf = d_factor_skolem.find( n );
  if( itf==d_factor_skolem.end() ){
    Node k = NodeManager::currentNM()->mkSkolem( "kf", n.getType() );
    Node k_eq = Rewriter::rewrite( k.eqNode( n ) );
    lemmas.push_back( k_eq );
    d_factor_skolem[n] = k;
    return k;
  }else{
    return itf->second;
  }  
}

std::vector<Node> NonlinearExtension::checkMonomialInferResBounds() {            
  std::vector< Node > lemmas; 
  Trace("nl-ext") << "Get monomial resolution inferred bound lemmas..." << std::endl;
  for (unsigned j = 0; j < d_mterms.size(); j++) {
    Node a = d_mterms[j];
    std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itca =
        d_ci.find(a);
    if (itca != d_ci.end()) {
      for (unsigned k = (j + 1); k < d_mterms.size(); k++) {
        Node b = d_mterms[k];
        std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator
            itcb = d_ci.find(b);
        if (itcb != d_ci.end()) {
          Trace("nl-ext-rbound-debug") << "resolution inferences : compare "
                                       << a << " and " << b << std::endl;
          // if they have common factors
          std::map<Node, Node>::iterator ita = d_mono_diff[a].find(b);
          if (ita != d_mono_diff[a].end()) {
            Trace("nl-ext-rbound") << "Get resolution inferences for [a] " << a
                                   << " vs [b] " << b << std::endl;
            std::map<Node, Node>::iterator itb = d_mono_diff[b].find(a);
            Assert(itb != d_mono_diff[b].end());
            Node mv_a = d_model.computeAbstractModelValue(ita->second);
            Assert(mv_a.isConst());
            int mv_a_sgn = mv_a.getConst<Rational>().sgn();
            if (mv_a_sgn == 0)
            {
              // we don't compare monomials whose current model value is zero
              continue;
            }
            Node mv_b = d_model.computeAbstractModelValue(itb->second);
            Assert(mv_b.isConst());
            int mv_b_sgn = mv_b.getConst<Rational>().sgn();
            if (mv_b_sgn == 0)
            {
              // we don't compare monomials whose current model value is zero
              continue;
            }
            Trace("nl-ext-rbound")
                << "  [a] factor is " << ita->second
                << ", sign in model = " << mv_a_sgn << std::endl;
            Trace("nl-ext-rbound")
                << "  [b] factor is " << itb->second
                << ", sign in model = " << mv_b_sgn << std::endl;

            std::vector<Node> exp;
            // bounds of a
            for (std::map<Node, std::map<Node, Kind> >::iterator itcac =
                     itca->second.begin();
                 itcac != itca->second.end(); ++itcac) {
              Node coeff_a = itcac->first;
              for (std::map<Node, Kind>::iterator itcar =
                       itcac->second.begin();
                   itcar != itcac->second.end(); ++itcar) {
                Node rhs_a = itcar->first;
                Node rhs_a_res_base =
                    NodeManager::currentNM()->mkNode(MULT, itb->second, rhs_a);
                rhs_a_res_base = Rewriter::rewrite(rhs_a_res_base);
                if (!hasNewMonomials(rhs_a_res_base, d_ms)) {
                  Kind type_a = itcar->second;
                  exp.push_back(d_ci_exp[a][coeff_a][rhs_a]);

                  // bounds of b
                  for (std::map<Node, std::map<Node, Kind> >::iterator itcbc =
                           itcb->second.begin();
                       itcbc != itcb->second.end(); ++itcbc) {
                    Node coeff_b = itcbc->first;
                    Node rhs_a_res =
                        ArithMSum::mkCoeffTerm(coeff_b, rhs_a_res_base);
                    for (std::map<Node, Kind>::iterator itcbr =
                             itcbc->second.begin();
                         itcbr != itcbc->second.end(); ++itcbr) {
                      Node rhs_b = itcbr->first;
                      Node rhs_b_res = NodeManager::currentNM()->mkNode(
                          MULT, ita->second, rhs_b);
                      rhs_b_res = ArithMSum::mkCoeffTerm(coeff_a, rhs_b_res);
                      rhs_b_res = Rewriter::rewrite(rhs_b_res);
                      if (!hasNewMonomials(rhs_b_res, d_ms)) {
                        Kind type_b = itcbr->second;
                        exp.push_back(d_ci_exp[b][coeff_b][rhs_b]);
                        if (Trace.isOn("nl-ext-rbound")) {
                          Trace("nl-ext-rbound") << "* try bounds : ";
                          debugPrintBound("nl-ext-rbound", coeff_a, a, type_a,
                                          rhs_a);
                          Trace("nl-ext-rbound") << std::endl;
                          Trace("nl-ext-rbound") << "               ";
                          debugPrintBound("nl-ext-rbound", coeff_b, b, type_b,
                                          rhs_b);
                          Trace("nl-ext-rbound") << std::endl;
                        }
                        Kind types[2];
                        for (unsigned r = 0; r < 2; r++) {
                          Node pivot_factor =
                              r == 0 ? itb->second : ita->second;
                          int pivot_factor_sign =
                              r == 0 ? mv_b_sgn : mv_a_sgn;
                          types[r] = r == 0 ? type_a : type_b;
                          if (pivot_factor_sign == (r == 0 ? 1 : -1)) {
                            types[r] = reverseRelationKind(types[r]);
                          }
                          if (pivot_factor_sign == 1) {
                            exp.push_back(NodeManager::currentNM()->mkNode(
                                GT, pivot_factor, d_zero));
                          } else {
                            exp.push_back(NodeManager::currentNM()->mkNode(
                                LT, pivot_factor, d_zero));
                          }
                        }
                        Kind jk = transKinds(types[0], types[1]);
                        Trace("nl-ext-rbound-debug")
                            << "trans kind : " << types[0] << " + "
                            << types[1] << " = " << jk << std::endl;
                        if (jk != UNDEFINED_KIND)
                        {
                          Node conc = NodeManager::currentNM()->mkNode(
                              jk, rhs_a_res, rhs_b_res);
                          Node conc_mv =
                              d_model.computeAbstractModelValue(conc);
                          if (conc_mv == d_false) {
                            Node rblem = NodeManager::currentNM()->mkNode(
                                IMPLIES,
                                NodeManager::currentNM()->mkNode(AND, exp),
                                conc);
                            Trace("nl-ext-rbound-lemma-debug")
                                << "Resolution bound lemma "
                                   "(pre-rewrite) "
                                   ": "
                                << rblem << std::endl;
                            rblem = Rewriter::rewrite(rblem);
                            Trace("nl-ext-rbound-lemma")
                                << "Resolution bound lemma : " << rblem
                                << std::endl;
                            lemmas.push_back(rblem);
                          }
                        }
                        exp.pop_back();
                        exp.pop_back();
                        exp.pop_back();
                      }
                    }
                  }
                  exp.pop_back();
                }
              }
            }
          }
        }
      }
    }
  }
  return lemmas;
}
                    
std::vector<Node> NonlinearExtension::checkTranscendentalInitialRefine() {
  std::vector< Node > lemmas;
  Trace("nl-ext") << "Get initial refinement lemmas for transcendental functions..." << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
  {
    Kind k = tfl.first;
    for (const Node& t : tfl.second)
    {
      //initial refinements
      if( d_tf_initial_refine.find( t )==d_tf_initial_refine.end() ){
        d_tf_initial_refine[t] = true;
        Node lem;
        if (k == SINE)
        {
          Node symn = NodeManager::currentNM()->mkNode(
              SINE, NodeManager::currentNM()->mkNode(MULT, d_neg_one, t[0]));
          symn = Rewriter::rewrite( symn );
          // Can assume it is its own master since phase is split over 0,
          // hence  -pi <= t[0] <= pi implies -pi <= -t[0] <= pi.
          d_trMaster[symn] = symn;
          d_trSlaves[symn].push_back(symn);
          Assert(d_trSlaves.find(t) != d_trSlaves.end());
          std::vector< Node > children;

          lem = NodeManager::currentNM()->mkNode(
              AND,
              // bounds
              NodeManager::currentNM()->mkNode(
                  AND,
                  NodeManager::currentNM()->mkNode(LEQ, t, d_one),
                  NodeManager::currentNM()->mkNode(GEQ, t, d_neg_one)),
              // symmetry
              NodeManager::currentNM()->mkNode(PLUS, t, symn).eqNode(d_zero),
              // sign
              NodeManager::currentNM()->mkNode(
                  EQUAL,
                  NodeManager::currentNM()->mkNode(LT, t[0], d_zero),
                  NodeManager::currentNM()->mkNode(LT, t, d_zero)),
              // zero val
              NodeManager::currentNM()->mkNode(
                  EQUAL,
                  NodeManager::currentNM()->mkNode(GT, t[0], d_zero),
                  NodeManager::currentNM()->mkNode(GT, t, d_zero)));
          lem = NodeManager::currentNM()->mkNode(
              AND,
              lem,
              // zero tangent
              NodeManager::currentNM()->mkNode(
                  AND,
                  NodeManager::currentNM()->mkNode(
                      IMPLIES,
                      NodeManager::currentNM()->mkNode(GT, t[0], d_zero),
                      NodeManager::currentNM()->mkNode(LT, t, t[0])),
                  NodeManager::currentNM()->mkNode(
                      IMPLIES,
                      NodeManager::currentNM()->mkNode(LT, t[0], d_zero),
                      NodeManager::currentNM()->mkNode(GT, t, t[0]))),
              // pi tangent
              NodeManager::currentNM()->mkNode(
                  AND,
                  NodeManager::currentNM()->mkNode(
                      IMPLIES,
                      NodeManager::currentNM()->mkNode(LT, t[0], d_pi),
                      NodeManager::currentNM()->mkNode(
                          LT,
                          t,
                          NodeManager::currentNM()->mkNode(MINUS, d_pi, t[0]))),
                  NodeManager::currentNM()->mkNode(
                      IMPLIES,
                      NodeManager::currentNM()->mkNode(GT, t[0], d_pi_neg),
                      NodeManager::currentNM()->mkNode(
                          GT,
                          t,
                          NodeManager::currentNM()->mkNode(
                              MINUS, d_pi_neg, t[0])))));
        }
        else if (k == EXPONENTIAL)
        {
          // ( exp(x) > 0 ) ^ ( x=0 <=> exp( x ) = 1 ) ^ ( x < 0 <=> exp( x ) <
          // 1 ) ^ ( x <= 0 V exp( x ) > x + 1 )
          lem = NodeManager::currentNM()->mkNode(
              AND,
              NodeManager::currentNM()->mkNode(GT, t, d_zero),
              NodeManager::currentNM()->mkNode(
                  EQUAL, t[0].eqNode(d_zero), t.eqNode(d_one)),
              NodeManager::currentNM()->mkNode(
                  EQUAL,
                  NodeManager::currentNM()->mkNode(LT, t[0], d_zero),
                  NodeManager::currentNM()->mkNode(LT, t, d_one)),
              NodeManager::currentNM()->mkNode(
                  OR,
                  NodeManager::currentNM()->mkNode(LEQ, t[0], d_zero),
                  NodeManager::currentNM()->mkNode(
                      GT,
                      t,
                      NodeManager::currentNM()->mkNode(PLUS, t[0], d_one))));
        }
        if( !lem.isNull() ){
          lemmas.push_back( lem );
        }
      }
    }
  }
  
  return lemmas;
}

std::vector<Node> NonlinearExtension::checkTranscendentalMonotonic() {
  std::vector< Node > lemmas;
  Trace("nl-ext") << "Get monotonicity lemmas for transcendental functions..." << std::endl;
  
  //sort arguments of all transcendentals
  std::map< Kind, std::vector< Node > > sorted_tf_args;
  std::map< Kind, std::map< Node, Node > > tf_arg_to_term;

  for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
  {
    Kind k = tfl.first;
    if (k == EXPONENTIAL || k == SINE)
    {
      for (const Node& tf : tfl.second)
      {
        Node a = tf[0];
        Node mvaa = d_model.computeAbstractModelValue(a);
        if (mvaa.isConst())
        {
          Trace("nl-ext-tf-mono-debug") << "...tf term : " << a << std::endl;
          sorted_tf_args[k].push_back(a);
          tf_arg_to_term[k][a] = tf;
        }
      }
    }
  }

  SortNlModel smv;
  smv.d_nlm = &d_model;
  //sort by concrete values
  smv.d_isConcrete = true;
  smv.d_reverse_order = true;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
  {
    Kind k = tfl.first;
    if( !sorted_tf_args[k].empty() ){
      std::sort( sorted_tf_args[k].begin(), sorted_tf_args[k].end(), smv );
      Trace("nl-ext-tf-mono") << "Sorted transcendental function list for " << k << " : " << std::endl;
      for (unsigned i = 0; i < sorted_tf_args[k].size(); i++)
      {
        Node targ = sorted_tf_args[k][i];
        Node mvatarg = d_model.computeAbstractModelValue(targ);
        Trace("nl-ext-tf-mono")
            << "  " << targ << " -> " << mvatarg << std::endl;
        Node t = tf_arg_to_term[k][targ];
        Node mvat = d_model.computeAbstractModelValue(t);
        Trace("nl-ext-tf-mono") << "     f-val : " << mvat << std::endl;
      }
      std::vector< Node > mpoints;
      std::vector< Node > mpoints_vals;
      if (k == SINE)
      {
        mpoints.push_back( d_pi );
        mpoints.push_back( d_pi_2 );
        mpoints.push_back(d_zero);
        mpoints.push_back( d_pi_neg_2 );
        mpoints.push_back( d_pi_neg );
      }
      else if (k == EXPONENTIAL)
      {
        mpoints.push_back( Node::null() );
      }
      if( !mpoints.empty() ){
        //get model values for points
        for( unsigned i=0; i<mpoints.size(); i++ ){
          Node mpv;
          if( !mpoints[i].isNull() ){
            mpv = d_model.computeAbstractModelValue(mpoints[i]);
            Assert(mpv.isConst());
          }
          mpoints_vals.push_back( mpv );
        }
        
        unsigned mdir_index = 0;
        int monotonic_dir = -1;
        Node mono_bounds[2];
        Node targ, targval, t, tval;
        for (unsigned i = 0, size = sorted_tf_args[k].size(); i < size; i++)
        {
          Node sarg = sorted_tf_args[k][i];
          Node sargval = d_model.computeAbstractModelValue(sarg);
          Assert(sargval.isConst());
          Node s = tf_arg_to_term[k][ sarg ];
          Node sval = d_model.computeAbstractModelValue(s);
          Assert(sval.isConst());

          //increment to the proper monotonicity region
          bool increment = true;
          while (increment && mdir_index < mpoints.size())
          {
            increment = false;
            if( mpoints[mdir_index].isNull() ){
              increment = true;
            }else{
              Node pval = mpoints_vals[mdir_index];
              Assert(pval.isConst());
              if( sargval.getConst<Rational>() < pval.getConst<Rational>() ){
                increment = true;
                Trace("nl-ext-tf-mono") << "...increment at " << sarg << " since model value is less than " << mpoints[mdir_index] << std::endl;
              }
            }
            if( increment ){
              tval = Node::null();
              mono_bounds[1] = mpoints[mdir_index];
              mdir_index++;
              monotonic_dir = regionToMonotonicityDir(k, mdir_index);
              if (mdir_index < mpoints.size())
              {
                mono_bounds[0] = mpoints[mdir_index];
              }else{
                mono_bounds[0] = Node::null();
              }
            }
          }
          // store the concavity region
          d_tf_region[s] = mdir_index;
          Trace("nl-ext-concavity") << "Transcendental function " << s
                                    << " is in region #" << mdir_index;
          Trace("nl-ext-concavity") << ", arg model value = " << sargval
                                    << std::endl;

          if( !tval.isNull() ){
            Node mono_lem;
            if( monotonic_dir==1 && sval.getConst<Rational>() > tval.getConst<Rational>() ){
              mono_lem = NodeManager::currentNM()->mkNode(
                  IMPLIES,
                  NodeManager::currentNM()->mkNode(GEQ, targ, sarg),
                  NodeManager::currentNM()->mkNode(GEQ, t, s));
            }else if( monotonic_dir==-1 && sval.getConst<Rational>() < tval.getConst<Rational>() ){
              mono_lem = NodeManager::currentNM()->mkNode(
                  IMPLIES,
                  NodeManager::currentNM()->mkNode(LEQ, targ, sarg),
                  NodeManager::currentNM()->mkNode(LEQ, t, s));
            }
            if( !mono_lem.isNull() ){        
              if( !mono_bounds[0].isNull() ){
                Assert(!mono_bounds[1].isNull());
                mono_lem = NodeManager::currentNM()->mkNode(
                    IMPLIES,
                    NodeManager::currentNM()->mkNode(
                        AND,
                        mkBounded(mono_bounds[0], targ, mono_bounds[1]),
                        mkBounded(mono_bounds[0], sarg, mono_bounds[1])),
                    mono_lem);
              }      
              Trace("nl-ext-tf-mono") << "Monotonicity lemma : " << mono_lem << std::endl;
              lemmas.push_back( mono_lem );
            }
          }
          // store the previous values
          targ = sarg;
          targval = sargval;
          t = s;
          tval = sval;
        }
      }
    }
  }
  return lemmas;
}

std::vector<Node> NonlinearExtension::checkTranscendentalTangentPlanes(
    std::map<Node, NlLemmaSideEffect>& lemSE)
{
  std::vector<Node> lemmas;
  Trace("nl-ext") << "Get tangent plane lemmas for transcendental functions..."
                  << std::endl;
  // this implements Figure 3 of "Satisfiaility Modulo Transcendental Functions
  // via Incremental Linearization" by Cimatti et al
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_funcMap)
  {
    Kind k = tfs.first;
    if (k == PI)
    {
      // We do not use Taylor approximation for PI currently.
      // This is because the convergence is extremely slow, and hence an
      // initial approximation is superior.
      continue;
    }
    Trace("nl-ext-tftp-debug2") << "Taylor variables: " << std::endl;
    Trace("nl-ext-tftp-debug2")
        << "          taylor_real_fv : " << d_taylor_real_fv << std::endl;
    Trace("nl-ext-tftp-debug2")
        << "     taylor_real_fv_base : " << d_taylor_real_fv_base << std::endl;
    Trace("nl-ext-tftp-debug2")
        << " taylor_real_fv_base_rem : " << d_taylor_real_fv_base_rem
        << std::endl;
    Trace("nl-ext-tftp-debug2") << std::endl;

    // we substitute into the Taylor sum P_{n,f(0)}( x )

    for (const Node& tf : tfs.second)
    {
      // tf is Figure 3 : tf( x )
      Trace("nl-ext-tftp") << "Compute tangent planes " << tf << std::endl;
      // go until max degree is reached, or we don't meet bound criteria
      for (unsigned d = 1; d <= d_taylor_degree; d++)
      {
        Trace("nl-ext-tftp") << "- run at degree " << d << "..." << std::endl;
        unsigned prev = lemmas.size();
        if (checkTfTangentPlanesFun(tf, d, lemmas, lemSE))
        {
          Trace("nl-ext-tftp")
              << "...fail, #lemmas = " << (lemmas.size() - prev) << std::endl;
          break;
        }
        else
        {
          Trace("nl-ext-tftp") << "...success" << std::endl;
        }
      }
    }
  }

  return lemmas;
}

bool NonlinearExtension::checkTfTangentPlanesFun(
    Node tf,
    unsigned d,
    std::vector<Node>& lemmas,
    std::map<Node, NlLemmaSideEffect>& lemSE)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = tf.getKind();
  // this should only be run on master applications
  Assert(d_trSlaves.find(tf) != d_trSlaves.end());

  // Figure 3 : c
  Node c = d_model.computeAbstractModelValue(tf[0]);
  int csign = c.getConst<Rational>().sgn();
  if (csign == 0)
  {
    // no secant/tangent plane is necessary
    return true;
  }
  Assert(csign == 1 || csign == -1);

  // Figure 3: P_l, P_u
  // mapped to for signs of c
  std::map<int, Node> poly_approx_bounds[2];
  std::vector<Node> pbounds;
  getPolynomialApproximationBoundForArg(k, c, d, pbounds);
  poly_approx_bounds[0][1] = pbounds[0];
  poly_approx_bounds[0][-1] = pbounds[1];
  poly_approx_bounds[1][1] = pbounds[2];
  poly_approx_bounds[1][-1] = pbounds[3];

  // Figure 3 : v
  Node v = d_model.computeAbstractModelValue(tf);

  // check value of tf
  Trace("nl-ext-tftp-debug") << "Process tangent plane refinement for " << tf
                             << ", degree " << d << "..." << std::endl;
  Trace("nl-ext-tftp-debug") << "  value in model : " << v << std::endl;
  Trace("nl-ext-tftp-debug") << "  arg value in model : " << c << std::endl;

  std::vector<Node> taylor_vars;
  taylor_vars.push_back(d_taylor_real_fv);

  // compute the concavity
  int region = -1;
  std::unordered_map<Node, int, NodeHashFunction>::iterator itr =
      d_tf_region.find(tf);
  if (itr != d_tf_region.end())
  {
    region = itr->second;
    Trace("nl-ext-tftp-debug") << "  region is : " << region << std::endl;
  }
  // Figure 3 : conc
  int concavity = regionToConcavity(k, itr->second);
  Trace("nl-ext-tftp-debug") << "  concavity is : " << concavity << std::endl;
  if (concavity == 0)
  {
    // no secant/tangent plane is necessary
    return true;
  }
  // bounds for which we are this concavity
  // Figure 3: < l, u >
  Node bounds[2];
  if (k == SINE)
  {
    bounds[0] = regionToLowerBound(k, region);
    Assert(!bounds[0].isNull());
    bounds[1] = regionToUpperBound(k, region);
    Assert(!bounds[1].isNull());
  }

  // Figure 3: P
  Node poly_approx;

  // compute whether this is a tangent refinement or a secant refinement
  bool is_tangent = false;
  bool is_secant = false;
  std::pair<Node, Node> mvb = getTfModelBounds(tf, d);
  for (unsigned r = 0; r < 2; r++)
  {
    Node pab = poly_approx_bounds[r][csign];
    Node v_pab = r == 0 ? mvb.first : mvb.second;
    if (!v_pab.isNull())
    {
      Trace("nl-ext-tftp-debug2") << "...model value of " << pab << " is "
                                  << v_pab << std::endl;

      Assert(v_pab.isConst());
      Node comp = nm->mkNode(r == 0 ? LT : GT, v, v_pab);
      Trace("nl-ext-tftp-debug2") << "...compare : " << comp << std::endl;
      Node compr = Rewriter::rewrite(comp);
      Trace("nl-ext-tftp-debug2") << "...got : " << compr << std::endl;
      if (compr == d_true)
      {
        // beyond the bounds
        if (r == 0)
        {
          poly_approx = poly_approx_bounds[r][csign];
          is_tangent = concavity == 1;
          is_secant = concavity == -1;
        }
        else
        {
          poly_approx = poly_approx_bounds[r][csign];
          is_tangent = concavity == -1;
          is_secant = concavity == 1;
        }
        if (Trace.isOn("nl-ext-tftp"))
        {
          Trace("nl-ext-tftp") << "*** Outside boundary point (";
          Trace("nl-ext-tftp") << (r == 0 ? "low" : "high") << ") ";
          printRationalApprox("nl-ext-tftp", v_pab);
          Trace("nl-ext-tftp") << ", will refine..." << std::endl;
          Trace("nl-ext-tftp") << "    poly_approx = " << poly_approx
                               << std::endl;
          Trace("nl-ext-tftp") << "    is_tangent = " << is_tangent
                               << std::endl;
          Trace("nl-ext-tftp") << "    is_secant = " << is_secant << std::endl;
        }
        break;
      }
      else
      {
        Trace("nl-ext-tftp") << "  ...within " << (r == 0 ? "low" : "high")
                             << " bound : ";
        printRationalApprox("nl-ext-tftp", v_pab);
        Trace("nl-ext-tftp") << std::endl;
      }
    }
  }

  // Figure 3: P( c )
  Node poly_approx_c;
  if (is_tangent || is_secant)
  {
    Assert(!poly_approx.isNull());
    std::vector<Node> taylor_subs;
    taylor_subs.push_back(c);
    Assert(taylor_vars.size() == taylor_subs.size());
    poly_approx_c = poly_approx.substitute(taylor_vars.begin(),
                                           taylor_vars.end(),
                                           taylor_subs.begin(),
                                           taylor_subs.end());
    Trace("nl-ext-tftp-debug2") << "...poly approximation at c is "
                                << poly_approx_c << std::endl;
  }
  else
  {
    // we may want to continue getting better bounds
    return false;
  }

  if (is_tangent)
  {
    // compute tangent plane
    // Figure 3: T( x )
    // We use zero slope tangent planes, since the concavity of the Taylor
    // approximation cannot be easily established.
    Node tplane = poly_approx_c;

    Node lem = nm->mkNode(concavity == 1 ? GEQ : LEQ, tf, tplane);
    std::vector<Node> antec;
    int mdir = regionToMonotonicityDir(k, region);
    for (unsigned i = 0; i < 2; i++)
    {
      // Tangent plane is valid in the interval [c,u) if the slope of the
      // function matches its concavity, and is valid in (l, c] otherwise.
      Node use_bound = (mdir == concavity) == (i == 0) ? c : bounds[i];
      if (!use_bound.isNull())
      {
        Node ant = nm->mkNode(i == 0 ? GEQ : LEQ, tf[0], use_bound);
        antec.push_back(ant);
      }
    }
    if (!antec.empty())
    {
      Node antec_n = antec.size() == 1 ? antec[0] : nm->mkNode(AND, antec);
      lem = nm->mkNode(IMPLIES, antec_n, lem);
    }
    Trace("nl-ext-tftp-debug2")
        << "*** Tangent plane lemma (pre-rewrite): " << lem << std::endl;
    lem = Rewriter::rewrite(lem);
    Trace("nl-ext-tftp-lemma") << "*** Tangent plane lemma : " << lem
                               << std::endl;
    Assert(d_model.computeAbstractModelValue(lem) == d_false);
    // Figure 3 : line 9
    lemmas.push_back(lem);
  }
  else if (is_secant)
  {
    // bounds are the minimum and maximum previous secant points
    // should not repeat secant points: secant lemmas should suffice to
    // rule out previous assignment
    Assert(std::find(
               d_secant_points[tf][d].begin(), d_secant_points[tf][d].end(), c)
           == d_secant_points[tf][d].end());
    // Insert into the (temporary) vector. We do not update this vector
    // until we are sure this secant plane lemma has been processed. We do
    // this by mapping the lemma to a side effect below.
    std::vector<Node> spoints = d_secant_points[tf][d];
    spoints.push_back(c);

    // sort
    SortNlModel smv;
    smv.d_nlm = &d_model;
    smv.d_isConcrete = true;
    std::sort(spoints.begin(), spoints.end(), smv);
    // get the resulting index of c
    unsigned index =
        std::find(spoints.begin(), spoints.end(), c) - spoints.begin();
    // bounds are the next closest upper/lower bound values
    if (index > 0)
    {
      bounds[0] = spoints[index - 1];
    }
    else
    {
      // otherwise, we use the lower boundary point for this concavity
      // region
      if (k == SINE)
      {
        Assert(!bounds[0].isNull());
      }
      else if (k == EXPONENTIAL)
      {
        // pick c-1
        bounds[0] = Rewriter::rewrite(nm->mkNode(MINUS, c, d_one));
      }
    }
    if (index < spoints.size() - 1)
    {
      bounds[1] = spoints[index + 1];
    }
    else
    {
      // otherwise, we use the upper boundary point for this concavity
      // region
      if (k == SINE)
      {
        Assert(!bounds[1].isNull());
      }
      else if (k == EXPONENTIAL)
      {
        // pick c+1
        bounds[1] = Rewriter::rewrite(nm->mkNode(PLUS, c, d_one));
      }
    }
    Trace("nl-ext-tftp-debug2") << "...secant bounds are : " << bounds[0]
                                << " ... " << bounds[1] << std::endl;

    // the secant plane may be conjunction of 1-2 guarded inequalities
    std::vector<Node> lemmaConj;
    for (unsigned s = 0; s < 2; s++)
    {
      // compute secant plane
      Assert(!poly_approx.isNull());
      Assert(!bounds[s].isNull());
      // take the model value of l or u (since may contain PI)
      Node b = d_model.computeAbstractModelValue(bounds[s]);
      Trace("nl-ext-tftp-debug2") << "...model value of bound " << bounds[s]
                                  << " is " << b << std::endl;
      Assert(b.isConst());
      if (c != b)
      {
        // Figure 3 : P(l), P(u), for s = 0,1
        Node poly_approx_b;
        std::vector<Node> taylor_subs;
        taylor_subs.push_back(b);
        Assert(taylor_vars.size() == taylor_subs.size());
        poly_approx_b = poly_approx.substitute(taylor_vars.begin(),
                                               taylor_vars.end(),
                                               taylor_subs.begin(),
                                               taylor_subs.end());
        // Figure 3: S_l( x ), S_u( x ) for s = 0,1
        Node splane;
        Node rcoeff_n = Rewriter::rewrite(nm->mkNode(MINUS, b, c));
        Assert(rcoeff_n.isConst());
        Rational rcoeff = rcoeff_n.getConst<Rational>();
        Assert(rcoeff.sgn() != 0);
        poly_approx_b = Rewriter::rewrite(poly_approx_b);
        poly_approx_c = Rewriter::rewrite(poly_approx_c);
        splane = nm->mkNode(
            PLUS,
            poly_approx_b,
            nm->mkNode(MULT,
                       nm->mkNode(MINUS, poly_approx_b, poly_approx_c),
                       nm->mkConst(Rational(1) / rcoeff),
                       nm->mkNode(MINUS, tf[0], b)));

        Node lem = nm->mkNode(concavity == 1 ? LEQ : GEQ, tf, splane);
        // With respect to Figure 3, this is slightly different.
        // In particular, we chose b to be the model value of bounds[s],
        // which is a constant although bounds[s] may not be (e.g. if it
        // contains PI).
        // To ensure that c...b does not cross an inflection point,
        // we guard with the symbolic version of bounds[s].
        // This leads to lemmas e.g. of this form:
        //   ( c <= x <= PI/2 ) => ( sin(x) < ( P( b ) - P( c ) )*( x -
        //   b ) + P( b ) )
        // where b = (PI/2)^M, the current value of PI/2 in the model.
        // This is sound since we are guarded by the symbolic
        // representation of PI/2.
        Node antec_n =
            nm->mkNode(AND,
                       nm->mkNode(GEQ, tf[0], s == 0 ? bounds[s] : c),
                       nm->mkNode(LEQ, tf[0], s == 0 ? c : bounds[s]));
        lem = nm->mkNode(IMPLIES, antec_n, lem);
        Trace("nl-ext-tftp-debug2")
            << "*** Secant plane lemma (pre-rewrite) : " << lem << std::endl;
        lem = Rewriter::rewrite(lem);
        Trace("nl-ext-tftp-lemma") << "*** Secant plane lemma : " << lem
                                   << std::endl;
        lemmaConj.push_back(lem);
        Assert(d_model.computeAbstractModelValue(lem) == d_false);
      }
    }
    // Figure 3 : line 22
    Assert(!lemmaConj.empty());
    Node lem =
        lemmaConj.size() == 1 ? lemmaConj[0] : nm->mkNode(AND, lemmaConj);
    lemmas.push_back(lem);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    lemSE[lem].d_secantPoint.push_back(std::make_tuple(tf, d, c));
  }
  return true;
}

int NonlinearExtension::regionToMonotonicityDir(Kind k, int region)
{
  if (k == EXPONENTIAL)
  {
    if (region == 1)
    {
      return 1;
    }
  }
  else if (k == SINE)
  {
    if (region == 1 || region == 4)
    {
      return -1;
    }
    else if (region == 2 || region == 3)
    {
      return 1;
    }
  }
  return 0;
}

int NonlinearExtension::regionToConcavity(Kind k, int region)
{
  if (k == EXPONENTIAL)
  {
    if (region == 1)
    {
      return 1;
    }
  }
  else if (k == SINE)
  {
    if (region == 1 || region == 2)
    {
      return -1;
    }
    else if (region == 3 || region == 4)
    {
      return 1;
    }
  }
  return 0;
}

Node NonlinearExtension::regionToLowerBound(Kind k, int region)
{
  if (k == SINE)
  {
    if (region == 1)
    {
      return d_pi_2;
    }
    else if (region == 2)
    {
      return d_zero;
    }
    else if (region == 3)
    {
      return d_pi_neg_2;
    }
    else if (region == 4)
    {
      return d_pi_neg;
    }
  }
  return Node::null();
}

Node NonlinearExtension::regionToUpperBound(Kind k, int region)
{
  if (k == SINE)
  {
    if (region == 1)
    {
      return d_pi;
    }
    else if (region == 2)
    {
      return d_pi_2;
    }
    else if (region == 3)
    {
      return d_zero;
    }
    else if (region == 4)
    {
      return d_pi_neg_2;
    }
  }
  return Node::null();
}

Node NonlinearExtension::getDerivative(Node n, Node x)
{
  Assert(x.isVar());
  // only handle the cases of the taylor expansion of d
  if (n.getKind() == EXPONENTIAL)
  {
    if (n[0] == x)
    {
      return n;
    }
  }
  else if (n.getKind() == SINE)
  {
    if (n[0] == x)
    {
      Node na = NodeManager::currentNM()->mkNode(MINUS, d_pi_2, n[0]);
      Node ret = NodeManager::currentNM()->mkNode(SINE, na);
      ret = Rewriter::rewrite(ret);
      return ret;
    }
  }
  else if (n.getKind() == PLUS)
  {
    std::vector<Node> dchildren;
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      // PLUS is flattened in rewriter, recursion depth is bounded by 1
      Node dc = getDerivative(n[i], x);
      if (dc.isNull())
      {
        return dc;
      }else{
        dchildren.push_back(dc);
      }
    }
    return NodeManager::currentNM()->mkNode(PLUS, dchildren);
  }
  else if (n.getKind() == MULT)
  {
    Assert(n[0].isConst());
    Node dc = getDerivative(n[1], x);
    if (!dc.isNull())
    {
      return NodeManager::currentNM()->mkNode(MULT, n[0], dc);
    }
  }
  else if (n.getKind() == NONLINEAR_MULT)
  {
    unsigned xcount = 0;
    std::vector<Node> children;
    unsigned xindex = 0;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      if (n[i] == x)
      {
        xcount++;
        xindex = i;
      }
      children.push_back(n[i]);
    }
    if (xcount == 0)
    {
      return d_zero;
    }
    else
    {
      children[xindex] = NodeManager::currentNM()->mkConst(Rational(xcount));
    }
    return NodeManager::currentNM()->mkNode(MULT, children);
  }
  else if (n.isVar())
  {
    return n == x ? d_one : d_zero;
  }
  else if (n.isConst())
  {
    return d_zero;
  }
  Trace("nl-ext-debug") << "No derivative computed for " << n;
  Trace("nl-ext-debug") << " for d/d{" << x << "}" << std::endl;
  return Node::null();
}

std::pair<Node, Node> NonlinearExtension::getTaylor(Node fa, unsigned n)
{
  Assert(n > 0);
  Node fac;  // what term we cache for fa
  if (fa[0] == d_zero)
  {
    // optimization : simpler to compute (x-fa[0])^n if we are centered around 0
    fac = fa;
  }
  else
  {
    // otherwise we use a standard factor a in (x-a)^n
    fac = NodeManager::currentNM()->mkNode(fa.getKind(), d_taylor_real_fv_base);
  }
  Node taylor_rem;
  Node taylor_sum;
  // check if we have already computed this Taylor series
  std::unordered_map<unsigned, Node>::iterator itt = d_taylor_sum[fac].find(n);
  if (itt == d_taylor_sum[fac].end())
  {
    Node i_exp_base;
    if (fa[0] == d_zero)
    {
      i_exp_base = d_taylor_real_fv;
    }
    else
    {
      i_exp_base = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
          MINUS, d_taylor_real_fv, d_taylor_real_fv_base));
    }
    Node i_derv = fac;
    Node i_fact = d_one;
    Node i_exp = d_one;
    int i_derv_status = 0;
    unsigned counter = 0;
    std::vector<Node> sum;
    do
    {
      counter++;
      if (fa.getKind() == EXPONENTIAL)
      {
        // unchanged
      }
      else if (fa.getKind() == SINE)
      {
        if (i_derv_status % 2 == 1)
        {
          Node arg = NodeManager::currentNM()->mkNode(
              PLUS, d_pi_2, d_taylor_real_fv_base);
          i_derv = NodeManager::currentNM()->mkNode(SINE, arg);
        }
        else
        {
          i_derv = fa;
        }
        if (i_derv_status >= 2)
        {
          i_derv = NodeManager::currentNM()->mkNode(MINUS, d_zero, i_derv);
        }
        i_derv = Rewriter::rewrite(i_derv);
        i_derv_status = i_derv_status == 3 ? 0 : i_derv_status + 1;
      }
      if (counter == (n + 1))
      {
        TNode x = d_taylor_real_fv_base;
        i_derv = i_derv.substitute(x, d_taylor_real_fv_base_rem);
      }
      Node curr = NodeManager::currentNM()->mkNode(
          MULT,
          NodeManager::currentNM()->mkNode(DIVISION, i_derv, i_fact),
          i_exp);
      if (counter == (n + 1))
      {
        taylor_rem = curr;
      }
      else
      {
        sum.push_back(curr);
        i_fact = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
            MULT,
            NodeManager::currentNM()->mkConst(Rational(counter)),
            i_fact));
        i_exp = Rewriter::rewrite(
            NodeManager::currentNM()->mkNode(MULT, i_exp_base, i_exp));
      }
    } while (counter <= n);
    taylor_sum =
        sum.size() == 1 ? sum[0] : NodeManager::currentNM()->mkNode(PLUS, sum);

    if (fac[0] != d_taylor_real_fv_base)
    {
      TNode x = d_taylor_real_fv_base;
      taylor_sum = taylor_sum.substitute(x, fac[0]);
    }

    // cache
    d_taylor_sum[fac][n] = taylor_sum;
    d_taylor_rem[fac][n] = taylor_rem;
  }
  else
  {
    taylor_sum = itt->second;
    Assert(d_taylor_rem[fac].find(n) != d_taylor_rem[fac].end());
    taylor_rem = d_taylor_rem[fac][n];
  }

  // must substitute for the argument if we were using a different lookup
  if (fa[0] != fac[0])
  {
    TNode x = d_taylor_real_fv_base;
    taylor_sum = taylor_sum.substitute(x, fa[0]);
  }
  return std::pair<Node, Node>(taylor_sum, taylor_rem);
}

void NonlinearExtension::getPolynomialApproximationBounds(
    Kind k, unsigned d, std::vector<Node>& pbounds)
{
  if (d_poly_bounds[k][d].empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node tft = nm->mkNode(k, d_zero);
    // n is the Taylor degree we are currently considering
    unsigned n = 2 * d;
    // n must be even
    std::pair<Node, Node> taylor = getTaylor(tft, n);
    Trace("nl-ext-tftp-debug2") << "Taylor for " << k
                                << " is : " << taylor.first << std::endl;
    Node taylor_sum = Rewriter::rewrite(taylor.first);
    Trace("nl-ext-tftp-debug2") << "Taylor for " << k
                                << " is (post-rewrite) : " << taylor_sum
                                << std::endl;
    Assert(taylor.second.getKind() == MULT);
    Assert(taylor.second.getNumChildren() == 2);
    Assert(taylor.second[0].getKind() == DIVISION);
    Trace("nl-ext-tftp-debug2") << "Taylor remainder for " << k << " is "
                                << taylor.second << std::endl;
    // ru is x^{n+1}/(n+1)!
    Node ru = nm->mkNode(DIVISION, taylor.second[1], taylor.second[0][1]);
    ru = Rewriter::rewrite(ru);
    Trace("nl-ext-tftp-debug2")
        << "Taylor remainder factor is (post-rewrite) : " << ru << std::endl;
    if (k == EXPONENTIAL)
    {
      pbounds.push_back(taylor_sum);
      pbounds.push_back(taylor_sum);
      pbounds.push_back(Rewriter::rewrite(
          nm->mkNode(MULT, taylor_sum, nm->mkNode(PLUS, d_one, ru))));
      pbounds.push_back(Rewriter::rewrite(nm->mkNode(PLUS, taylor_sum, ru)));
    }
    else
    {
      Assert(k == SINE);
      Node l = Rewriter::rewrite(nm->mkNode(MINUS, taylor_sum, ru));
      Node u = Rewriter::rewrite(nm->mkNode(PLUS, taylor_sum, ru));
      pbounds.push_back(l);
      pbounds.push_back(l);
      pbounds.push_back(u);
      pbounds.push_back(u);
    }
    Trace("nl-ext-tf-tplanes") << "Polynomial approximation for " << k
                               << " is: " << std::endl;
    Trace("nl-ext-tf-tplanes") << " Lower (pos): " << pbounds[0] << std::endl;
    Trace("nl-ext-tf-tplanes") << " Upper (pos): " << pbounds[2] << std::endl;
    Trace("nl-ext-tf-tplanes") << " Lower (neg): " << pbounds[1] << std::endl;
    Trace("nl-ext-tf-tplanes") << " Upper (neg): " << pbounds[3] << std::endl;
    d_poly_bounds[k][d].insert(
        d_poly_bounds[k][d].end(), pbounds.begin(), pbounds.end());
  }
  else
  {
    pbounds.insert(
        pbounds.end(), d_poly_bounds[k][d].begin(), d_poly_bounds[k][d].end());
  }
}

void NonlinearExtension::getPolynomialApproximationBoundForArg(
    Kind k, Node c, unsigned d, std::vector<Node>& pbounds)
{
  getPolynomialApproximationBounds(k, d, pbounds);
  Assert(c.isConst());
  if (k == EXPONENTIAL && c.getConst<Rational>().sgn() == 1)
  {
    NodeManager* nm = NodeManager::currentNM();
    Node tft = nm->mkNode(k, d_zero);
    bool success = false;
    unsigned ds = d;
    TNode ttrf = d_taylor_real_fv;
    TNode tc = c;
    do
    {
      success = true;
      unsigned n = 2 * ds;
      std::pair<Node, Node> taylor = getTaylor(tft, n);
      // check that 1-c^{n+1}/(n+1)! > 0
      Node ru = nm->mkNode(DIVISION, taylor.second[1], taylor.second[0][1]);
      Node rus = ru.substitute(ttrf, tc);
      rus = Rewriter::rewrite(rus);
      Assert(rus.isConst());
      if (rus.getConst<Rational>() > d_one.getConst<Rational>())
      {
        success = false;
        ds = ds + 1;
      }
    } while (!success);
    if (ds > d)
    {
      Trace("nl-ext-exp-taylor")
          << "*** Increase Taylor bound to " << ds << " > " << d << " for ("
          << k << " " << c << ")" << std::endl;
      // must use sound upper bound
      std::vector<Node> pboundss;
      getPolynomialApproximationBounds(k, ds, pboundss);
      pbounds[2] = pboundss[2];
    }
  }
}

std::pair<Node, Node> NonlinearExtension::getTfModelBounds(Node tf, unsigned d)
{
  // compute the model value of the argument
  Node c = d_model.computeAbstractModelValue(tf[0]);
  Assert(c.isConst());
  int csign = c.getConst<Rational>().sgn();
  Kind k = tf.getKind();
  if (csign == 0)
  {
    // at zero, its trivial
    if (k == SINE)
    {
      return std::pair<Node, Node>(d_zero, d_zero);
    }
    Assert(k == EXPONENTIAL);
    return std::pair<Node, Node>(d_one, d_one);
  }
  bool isNeg = csign == -1;

  std::vector<Node> pbounds;
  getPolynomialApproximationBoundForArg(k, c, d, pbounds);

  std::vector<Node> bounds;
  TNode tfv = d_taylor_real_fv;
  TNode tfs = tf[0];
  for (unsigned d2 = 0; d2 < 2; d2++)
  {
    int index = d2 == 0 ? (isNeg ? 1 : 0) : (isNeg ? 3 : 2);
    Node pab = pbounds[index];
    if (!pab.isNull())
    {
      // { x -> tf[0] }
      pab = pab.substitute(tfv, tfs);
      pab = Rewriter::rewrite(pab);
      Node v_pab = d_model.computeAbstractModelValue(pab);
      bounds.push_back(v_pab);
    }
    else
    {
      bounds.push_back(Node::null());
    }
  }
  return std::pair<Node, Node>(bounds[0], bounds[1]);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
