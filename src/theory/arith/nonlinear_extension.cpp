/*********************                                                        */
/*! \file nonlinear_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

#include <set>

#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
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

// Returns map[key] if key is in map or Node::null() otherwise.
Node getNodeOrNull(const std::map<Node, Node>& map, Node key) {
  std::map<Node, Node>::const_iterator it = map.find(key);
  return (it == map.end()) ? Node::null() : it->second;
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

struct SubstitutionConstResult {
  // The resulting term of the substitution.
  Node term;

  // ?
  std::vector<Node> const_exp;

  // ??
  // A term sum[i] for which for rep_sum[i] not in rep_to_const.
  Node variable_term;
}; /* struct SubstitutionConstResult */

SubstitutionConstResult getSubstitutionConst(
    Node n, Node n_rsu, Node rsu_exp,
    const std::vector<Node>& sum, const std::vector<Node>& rep_sum,
    const std::map<Node, Node>& rep_to_const,
    const std::map<Node, Node>& rep_to_const_exp,
    const std::map<Node, Node>& rep_to_const_base) {
  Assert(sum.size() == rep_sum.size());

  SubstitutionConstResult result;

  std::vector<Node> vars;
  std::vector<Node> subs;
  std::set<Node> rep_exp_proc;
  for (unsigned i = 0; i < rep_sum.size(); i++) {
    Node cr = rep_sum[i];
    Node const_of_cr = getNodeOrNull(rep_to_const, cr);
    if (const_of_cr.isNull()) {
      result.variable_term = sum[i];
      continue;
    }
    Assert(!const_of_cr.isNull());
    Node const_base_of_cr = getNodeOrNull(rep_to_const_base, cr);
    Assert(!const_base_of_cr.isNull());
    if (const_base_of_cr != sum[i]) {
      result.const_exp.push_back(const_base_of_cr.eqNode(sum[i]));
    }
    if (rep_exp_proc.find(cr) == rep_exp_proc.end()) {
      rep_exp_proc.insert(cr);
      Node const_exp = getNodeOrNull(rep_to_const_exp, cr);
      if (!const_exp.isNull()) {
        result.const_exp.push_back(const_exp);
      }
    }
    vars.push_back(sum[i]);
    subs.push_back(const_of_cr);
  }
  if( n!=n_rsu && !rsu_exp.isNull() ){
    result.const_exp.push_back( rsu_exp );
  }
  Node substituted =
      n_rsu.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  result.term = Rewriter::rewrite(substituted);
  return result;
}

struct SortNonlinearExtension {
  SortNonlinearExtension()
      : d_nla(NULL), d_order_type(0), d_reverse_order(false) {}
  NonlinearExtension* d_nla;
  unsigned d_order_type;
  bool d_reverse_order;
  bool operator()(Node i, Node j) {
    int cv = d_nla->compare(i, j, d_order_type);
    if (cv == 0) {
      return i < j;
    } else {
      return d_reverse_order ? cv < 0 : cv > 0;
    }
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
    : d_def_lemmas(containing.getUserContext()),
      d_lemmas(containing.getUserContext()),
      d_zero_split(containing.getUserContext()),
      d_skolem_atoms(containing.getUserContext()),
      d_containing(containing),
      d_ee(ee),
      d_needsLastCall(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
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

class NonLinearExtentionSubstitutionSolver {
 public:
  NonLinearExtentionSubstitutionSolver(const eq::EqualityEngine* ee)
      : d_ee(ee) {}

  bool solve(const std::vector<Node>& vars, std::vector<Node>* subs,
             std::map<Node, std::vector<Node> >* exp,
             std::map<Node, std::vector<int> >* rep_to_subs_index);

 private:
  bool setSubstitutionConst(
      const std::vector<Node>& vars, Node r, Node r_c, Node r_cb,
      const std::vector<Node>& r_c_exp, std::vector<Node>* subs,
      std::map<Node, std::vector<Node> >* exp,
      std::map<Node, std::vector<int> >* rep_to_subs_index);

  const eq::EqualityEngine* d_ee;

  std::map<Node, Node > d_rep_sum_unique;
  std::map<Node, Node > d_rep_sum_unique_exp;

  std::map<Node, Node> d_rep_to_const;
  std::map<Node, Node> d_rep_to_const_exp;
  std::map<Node, Node> d_rep_to_const_base;

  // key in term_to_sum iff key in term_to_rep_sum.
  std::map<Node, std::vector<Node> > d_term_to_sum;
  std::map<Node, std::vector<Node> > d_term_to_rep_sum;
  std::map<Node, int> d_term_to_nconst_rep_count;

  std::map<Node, std::vector<Node> > d_reps_to_parent_terms;
  std::map<Node, std::vector<Node> > d_reps_to_terms;
};

bool NonLinearExtentionSubstitutionSolver::solve(
    const std::vector<Node>& vars, std::vector<Node>* subs,
    std::map<Node, std::vector<Node> >* exp,
    std::map<Node, std::vector<int> >* rep_to_subs_index) {
  // std::map<Node, Node> rep_to_const;
  // std::map<Node, Node> rep_to_const_exp;
  // std::map<Node, Node> rep_to_const_base;

  // std::map<Node, std::vector<Node> > term_to_sum;
  // std::map<Node, std::vector<Node> > term_to_rep_sum;
  // std::map<Node, int> term_to_nconst_rep_count;
  // std::map<Node, std::vector<Node> > reps_to_parent_terms;
  // std::map<Node, std::vector<Node> > reps_to_terms;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_ee);

  bool retVal = false;
  while (!eqcs_i.isFinished() && !rep_to_subs_index->empty()) {
    Node r = (*eqcs_i);
    if (r.getType().isReal()) {
      Trace("nl-subs-debug")
          << "Process equivalence class " << r << "..." << std::endl;
      Node r_c;
      Node r_cb;
      std::vector<Node> r_c_exp;
      if (r.isConst()) {
        r_c = r;
        r_cb = r;
      }
      // scan the class
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, d_ee);
      while (!eqc_i.isFinished()) {
        Node n = (*eqc_i);
        if (!n.isConst()) {
          Trace("nl-subs-debug") << "Look at term : " << n << std::endl;
          std::map<Node, Node> msum;
          if (ArithMSum::getMonomialSum(n, msum))
          {
            int nconst_count = 0;
            bool evaluatable = true;
            //first, collect sums of equal terms
            std::map< Node, Node > rep_to_mon;
            std::vector< Node > subs_rm;
            std::vector< Node > vars_rm;
            std::vector< Node > exp_rm;
            for (std::map<Node, Node>::iterator itm = msum.begin();
                 itm != msum.end(); ++itm) {
              if (!itm->first.isNull()) {
                if (d_ee->hasTerm(itm->first)) {
                  Node cr = d_ee->getRepresentative(itm->first);
                  std::map< Node, Node >::iterator itrm = rep_to_mon.find( cr );
                  if( itrm==rep_to_mon.end() ){
                    rep_to_mon[cr] = itm->first;
                  }else{
                    vars_rm.push_back( itm->first );
                    subs_rm.push_back( itrm->second );
                    exp_rm.push_back( itm->first.eqNode( itrm->second ) );
                  }
                }
              }else{
                Trace("nl-subs-debug")
                    << "...is not evaluatable due to monomial " << itm->first
                    << std::endl;
                evaluatable = false;
                break;
              }
            }
            if( evaluatable ){
              bool success = true;
              if( !vars_rm.empty() ){
                Node ns = n.substitute( vars_rm.begin(), vars_rm.end(), subs_rm.begin(), subs_rm.end() );
                ns = Rewriter::rewrite( ns );
                if( ns.isConst() ){
                  success = false;
                  if( r_c.isNull() ){
                    r_c = ns;
                    r_cb = n;
                    r_c_exp.insert( r_c_exp.end(), exp_rm.begin(), exp_rm.end() );
                  }
                }else{
                  //recompute the monomial
                  msum.clear();
                  if (!ArithMSum::getMonomialSum(ns, msum))
                  {
                    success = false;
                  }else{
                    d_rep_sum_unique_exp[n] =
                        exp_rm.size() == 1
                            ? exp_rm[0]
                            : NodeManager::currentNM()->mkNode(AND, exp_rm);
                    d_rep_sum_unique[n] = ns;
                  }
                }
              }else{
                d_rep_sum_unique[n] = n;
              }
              if( success ){
                for (std::map<Node, Node>::iterator itm = msum.begin();
                     itm != msum.end(); ++itm) {
                  if (!itm->first.isNull()) {
                    if (d_ee->hasTerm(itm->first)) {
                      Trace("nl-subs-debug")
                          << "      ...monomial " << itm->first << std::endl;
                      Node cr = d_ee->getRepresentative(itm->first);
                      d_term_to_sum[n].push_back(itm->first);
                      d_term_to_rep_sum[n].push_back(cr);
                      if (!Contains(d_rep_to_const, cr)) {
                        if (!IsInVector(d_reps_to_parent_terms[cr], n)) {
                          d_reps_to_parent_terms[cr].push_back(n);
                          nconst_count++;
                        }
                      }
                    } else {
                      Assert( false );
                    }
                  }
                }
                if (evaluatable) {
                  Trace("nl-subs-debug")
                      << "  ...term has " << nconst_count
                      << " unique non-constant represenative children."
                      << std::endl;
                  if (nconst_count == 0) {
                    if (r_c.isNull()) {
                      const SubstitutionConstResult result = getSubstitutionConst(
                          n, d_rep_sum_unique[n], d_rep_sum_unique_exp[n],
                          d_term_to_sum[n], d_term_to_rep_sum[n], d_rep_to_const,
                          d_rep_to_const_exp, d_rep_to_const_base);
                      r_c_exp.insert(r_c_exp.end(), result.const_exp.begin(),
                                     result.const_exp.end());
                      r_c = result.term;
                      r_cb = n;
                      Assert(result.variable_term.isNull());
                      Assert(r_c.isConst());
                    }
                  } else {
                    d_reps_to_terms[r].push_back(n);
                    d_term_to_nconst_rep_count[n] = nconst_count;
                  }
                }
              }
            }
          } else {
            Trace("nl-subs-debug")
                << "...could not get monomial sum " << std::endl;
          }
        }
        ++eqc_i;
      }
      if (!r_c.isNull()) {
        setSubstitutionConst(vars, r, r_c, r_cb, r_c_exp, subs, exp,
                             rep_to_subs_index);
      }
    }
    ++eqcs_i;
  }
  return retVal;
}

bool NonLinearExtentionSubstitutionSolver::setSubstitutionConst(
    const std::vector<Node>& vars, Node r, Node r_c, Node r_cb,
    const std::vector<Node>& r_c_exp, std::vector<Node>* subs,
    std::map<Node, std::vector<Node> >* exp,
    std::map<Node, std::vector<int> >* rep_to_subs_index) {
  Trace("nl-subs-debug") << "Set constant equivalence class : " << r << " -> "
                         << r_c << std::endl;
  bool retVal = false;

  d_rep_to_const[r] = r_c;
  Node expn;
  if (!r_c_exp.empty()) {
    expn = r_c_exp.size() == 1 ? r_c_exp[0]
                               : NodeManager::currentNM()->mkNode(AND, r_c_exp);
    Trace("nl-subs-debug") << "...explanation is " << expn << std::endl;
    d_rep_to_const_exp[r] = expn;
  }
  d_rep_to_const_base[r] = r_cb;

  std::map<Node, std::vector<int> >::const_iterator iti =
      rep_to_subs_index->find(r);
  if (iti != rep_to_subs_index->end()) {
    for (unsigned i = 0; i < iti->second.size(); i++) {
      int ii = iti->second[i];
      (*subs)[ii] = r_c;
      std::vector<Node>& exp_var_ii = (*exp)[vars[ii]];
      exp_var_ii.clear();
      if (!expn.isNull()) {
        exp_var_ii.push_back(expn);
      }
      if (vars[ii] != r_cb) {
        exp_var_ii.push_back(vars[ii].eqNode(r_cb));
      }
    }
    retVal = true;
    rep_to_subs_index->erase(r);
    if (rep_to_subs_index->empty()) {
      return retVal;
    }
  }

  // new inferred constants
  std::map<Node, Node> new_const;
  std::map<Node, std::vector<Node> > new_const_exp;

  // parent terms now evaluate to constants
  std::map<Node, std::vector<Node> >::const_iterator itrp =
      d_reps_to_parent_terms.find(r);
  if (itrp != d_reps_to_parent_terms.end()) {
    // Trace("nl-subs-debug") << "Look at " << itrp->second.size() << " parent
    // terms." << std::endl;
    for (unsigned i = 0; i < itrp->second.size(); i++) {
      Node m = itrp->second[i];
      d_term_to_nconst_rep_count[m]--;
      Node r = d_ee->getRepresentative(m);
      if (d_term_to_nconst_rep_count[m] == 0) {
        if (!Contains(d_rep_to_const, r)) {
          Trace("nl-subs-debug") << "...parent term " << m
                                 << " evaluates to constant." << std::endl;
          if (!Contains(new_const, m)) {
            const SubstitutionConstResult result = getSubstitutionConst(
                m, d_rep_sum_unique[m], d_rep_sum_unique_exp[m],
                d_term_to_sum[m], d_term_to_rep_sum[m], d_rep_to_const,
                d_rep_to_const_exp, d_rep_to_const_base);
            new_const_exp[m].insert(new_const_exp[m].end(),
                                    result.const_exp.begin(),
                                    result.const_exp.end());
            Node m_c = result.term;
            // count should be accurate
            Assert(result.variable_term.isNull());
            Assert(m_c.isConst());
            new_const[m] = m_c;
          }
        }
      } else if (d_term_to_nconst_rep_count[m] == 1) {
        // check if it is now univariate solved
        if (Contains(d_rep_to_const, r)) {
          Trace("nl-subs-debug") << "...parent term " << m
                                 << " is univariate solved." << std::endl;
          const SubstitutionConstResult result = getSubstitutionConst(
              m, d_rep_sum_unique[m], d_rep_sum_unique_exp[m],
              d_term_to_sum[m], d_term_to_rep_sum[m], d_rep_to_const,
              d_rep_to_const_exp, d_rep_to_const_base);
          Node eq = (result.term).eqNode(d_rep_to_const[r]);
          Node v_c = ArithMSum::solveEqualityFor(eq, result.variable_term);
          if (!v_c.isNull()) {
            Assert(v_c.isConst());
            if (Contains(new_const, result.variable_term)) {
              new_const[result.variable_term] = v_c;
              std::vector<Node>& explanation =
                  new_const_exp[result.variable_term];
              explanation.insert(explanation.end(), result.const_exp.begin(),
                                 result.const_exp.end());
              if (m != d_rep_to_const_base[r]) {
                explanation.push_back(m.eqNode(d_rep_to_const_base[r]));
              }
            }
          }
        }
      }
    }
  }

  // equal univariate terms now solved
  std::map<Node, std::vector<Node> >::iterator itt = d_reps_to_terms.find(r);
  if (itt != d_reps_to_terms.end()) {
    for (unsigned i = 0; i < itt->second.size(); i++) {
      Node m = itt->second[i];
      if (d_term_to_nconst_rep_count[m] == 1) {
        Trace("nl-subs-debug")
            << "...term " << m << " is univariate solved." << std::endl;
        const SubstitutionConstResult result = getSubstitutionConst(
            m, d_rep_sum_unique[m], d_rep_sum_unique_exp[m],
            d_term_to_sum[m], d_term_to_rep_sum[m], d_rep_to_const,
            d_rep_to_const_exp, d_rep_to_const_base);
        Node v = result.variable_term;
        Node m_t = result.term;
        Node eq = m_t.eqNode(r_c);
        Node v_c = ArithMSum::solveEqualityFor(eq, v);
        Trace("nl-subs-debug") << "Solved equality " << eq << " for " << v << ", got = " << v_c << std::endl;
        if (!v_c.isNull()) {
          Assert(v_c.isConst());
          if (new_const.find(v) == new_const.end()) {
            new_const[v] = v_c;
            new_const_exp[v].insert(new_const_exp[v].end(),
                                    result.const_exp.begin(),
                                    result.const_exp.end());
            if (m != r_cb) {
              new_const_exp[v].push_back(m.eqNode(r_cb));
            }
          }
        }
      }
    }
  }

  // now, process new inferred constants
  for (std::map<Node, Node>::iterator itn = new_const.begin();
       itn != new_const.end(); ++itn) {
    Node m = itn->first;
    Node r = d_ee->getRepresentative(m);
    if (!Contains(d_rep_to_const, r)) {
      if (setSubstitutionConst(vars, r, itn->second, m, new_const_exp[m], subs,
                               exp, rep_to_subs_index)) {
        retVal = true;
      }
    }
  }
  return retVal;
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

  if (options::nlExtSolveSubs()) {
    NonLinearExtentionSubstitutionSolver substitution_solver(d_ee);
    if (substitution_solver.solve(vars, &subs, &exp, &rep_to_subs_index)) {
      retVal = true;
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

Node NonlinearExtension::computeModelValue(Node n, unsigned index) {
  std::map<Node, Node>::iterator it = d_mv[index].find(n);
  if (it != d_mv[index].end()) {
    return it->second;
  } else {
    Trace("nl-ext-mv-debug") << "computeModelValue " << n << ", index=" << index << std::endl;
    Node ret;
    if (n.isConst()) {
      ret = n;
    }
    else if (index == 1 && (n.getKind() == NONLINEAR_MULT
                            || isTranscendentalKind(n.getKind())))
    {
      if (d_containing.getValuation().getModel()->hasTerm(n)) {
        // use model value for abstraction
        ret = d_containing.getValuation().getModel()->getRepresentative(n);
      } else {
        // abstraction does not exist, use model value
        //ret = computeModelValue(n, 0);
        ret = d_containing.getValuation().getModel()->getValue(n);
      }
      //Assert( ret.isConst() );
    } else if (n.getNumChildren() == 0) {
      if (n.getKind() == PI)
      {
        // we are interested in the exact value of PI, which cannot be computed.
        // hence, we return PI itself when asked for the concrete value.
        ret = n;
      }else{
        ret = d_containing.getValuation().getModel()->getValue(n);
      }
    } else {    
      // otherwise, compute true value
      std::vector<Node> children;
      if (n.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      for (unsigned i = 0; i < n.getNumChildren(); i++) {
        Node mc = computeModelValue(n[i], index);
        children.push_back(mc);
      }
      ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
      if (n.getKind() == APPLY_UF)
      {
        ret = d_containing.getValuation().getModel()->getValue(ret);
      }else{
        ret = Rewriter::rewrite(ret);
      }
          /*
      if (!ret.isConst()) {
        Trace("nl-ext-debug") << "...got non-constant : " << ret << " for "
                              << n << ", ask model directly." << std::endl;
        ret = d_containing.getValuation().getModel()->getValue(ret);
      }
      */
    }
    //if (ret.getType().isReal() && !isArithKind(n.getKind())) {
      // Trace("nl-ext-mv-debug") << ( index==0 ? "M" : "M_A" ) << "[ " << n
      // << " ] -> " << ret << std::endl;
      //may involve transcendental functions
      //Assert(ret.isConst());
    //}
    Trace("nl-ext-mv-debug") << "computed " << (index == 0 ? "M" : "M_A") << "["
                             << n << "] = " << ret << std::endl;
    d_mv[index][n] = ret;
    return ret;
  }
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

Node NonlinearExtension::mkLit(Node a, Node b, int status, int orderType) {
  if (status == 0) {
    Node a_eq_b = a.eqNode(b);
    if (orderType == 0) {
      return a_eq_b;
    } else {
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
    if (orderType == 0) {
      return nm->mkNode(greater_op, a, b);
    } else {
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

// by a <k1> b, a <k2> b, we know a <ret> b
Kind NonlinearExtension::joinKinds(Kind k1, Kind k2) {
  if (k2 < k1) {
    return joinKinds(k2, k1);
  } else if (k1 == k2) {
    return k1;
  } else {
    Assert(k1 == EQUAL || k1 == LT || k1 == LEQ || k1 == GT || k1 == GEQ);
    Assert(k2 == EQUAL || k2 == LT || k2 == LEQ || k2 == GT || k2 == GEQ);
    if (k1 == EQUAL)
    {
      if (k2 == LEQ || k2 == GEQ)
      {
        return k1;
      }
    }
    else if (k1 == LT)
    {
      if (k2 == LEQ)
      {
        return k1;
      }
    }
    else if (k1 == LEQ)
    {
      if (k2 == GEQ)
      {
        return EQUAL;
      }
    }
    else if (k1 == GT)
    {
      if (k2 == GEQ)
      {
        return k1;
      }
    }
    return UNDEFINED_KIND;
  }
}

// by a <k1> b, b <k2> c, we know a <ret> c
Kind NonlinearExtension::transKinds(Kind k1, Kind k2) {
  if (k2 < k1) {
    return transKinds(k2, k1);
  } else if (k1 == k2) {
    return k1;
  } else {
    Assert(k1 == EQUAL || k1 == LT || k1 == LEQ || k1 == GT || k1 == GEQ);
    Assert(k2 == EQUAL || k2 == LT || k2 == LEQ || k2 == GT || k2 == GEQ);
    if (k1 == EQUAL)
    {
      return k2;
    }
    else if (k1 == LT)
    {
      if (k2 == LEQ)
      {
        return k1;
      }
    }
    else if (k1 == GT)
    {
      if (k2 == GEQ)
      {
        return k1;
      }
    }
    return UNDEFINED_KIND;
  }
}

bool NonlinearExtension::isTranscendentalKind(Kind k) {
  // many operators are eliminated during rewriting
  Assert(k != TANGENT && k != COSINE && k != COSECANT && k != SECANT
         && k != COTANGENT);
  return k == EXPONENTIAL || k == SINE || k == PI;
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

int NonlinearExtension::flushLemma(Node lem) {
  Trace("nl-ext-lemma-debug")
      << "NonlinearExtension::Lemma pre-rewrite : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if (Contains(d_lemmas, lem)) {
    Trace("nl-ext-lemma-debug")
        << "NonlinearExtension::Lemma duplicate : " << lem << std::endl;
    // should not generate duplicates
    // Assert( false );
    return 0;
  }
  d_lemmas.insert(lem);
  Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : " << lem << std::endl;
  d_containing.getOutputChannel().lemma(lem);
  return 1;
}

int NonlinearExtension::flushLemmas(std::vector<Node>& lemmas) {
  if (options::nlExtEntailConflicts()) {
    // check if any are entailed to be false
    for (unsigned i = 0; i < lemmas.size(); i++) {
      Node ch_lemma = lemmas[i].negate();
      ch_lemma = Rewriter::rewrite(ch_lemma);
      Trace("nl-ext-et-debug")
          << "Check entailment of " << ch_lemma << "..." << std::endl;
      std::pair<bool, Node> et = d_containing.getValuation().entailmentCheck(
          THEORY_OF_TYPE_BASED, ch_lemma);
      Trace("nl-ext-et-debug") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
      if (et.first) {
        Trace("nl-ext-et") << "*** Lemma entailed to be in conflict : "
                           << lemmas[i] << std::endl;
        // return just this lemma
        if (flushLemma(lemmas[i])) {
          lemmas.clear();
          return 1;
        }
      }
    }
  }

  int sum = 0;
  for (unsigned i = 0; i < lemmas.size(); i++) {
    sum += flushLemma(lemmas[i]);
  }
  lemmas.clear();
  return sum;
}

std::vector<Node> NonlinearExtension::checkModel(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (size_t i = 0; i < assertions.size(); ++i) {
    Node lit = assertions[i];
    Node atom = lit.getKind()==NOT ? lit[0] : lit;
    if( d_skolem_atoms.find( atom )==d_skolem_atoms.end() ){
      Node litv = computeModelValue(lit);
      Trace("nl-ext-mv") << "M[[ " << lit << " ]] -> " << litv;
      if (litv != d_true) {
        Trace("nl-ext-mv") << " [model-false]" << std::endl;
        //Assert(litv == d_false);
        false_asserts.push_back(lit);
      } else {
        Trace("nl-ext-mv") << std::endl;
      }
    }
  }
  return false_asserts;
}

bool NonlinearExtension::checkModelTf(const std::vector<Node>& assertions)
{
  Trace("nl-ext-tf-check-model") << "check-model : Run" << std::endl;
  // add bounds for PI
  d_tf_check_model_bounds[d_pi] =
      std::pair<Node, Node>(d_pi_bound[0], d_pi_bound[1]);
  for (const std::pair<const Node, std::pair<Node, Node> >& tfb :
       d_tf_check_model_bounds)
  {
    Node tf = tfb.first;
    Trace("nl-ext-tf-check-model")
        << "check-model : satisfied approximate bound : ";
    Trace("nl-ext-tf-check-model") << tfb.second.first << " <= " << tf
                                   << " <= " << tfb.second.second << std::endl;
  }

  std::vector<Node> check_assertions;
  for (const Node& a : assertions)
  {
    Node av = computeModelValue(a);
    // simple check
    if (!simpleCheckModelTfLit(av))
    {
      check_assertions.push_back(av);
      Trace("nl-ext-tf-check-model") << "check-model : assertion : " << av
                                     << " (from " << a << ")" << std::endl;
    }
  }

  if (check_assertions.empty())
  {
    Trace("nl-ext-tf-check-model") << "...simple check succeeded." << std::endl;
    return true;
  }
  else
  {
    Trace("nl-ext-tf-check-model") << "...simple check failed." << std::endl;
    // TODO (#1450) check model for general case
    return false;
  }
}

bool NonlinearExtension::simpleCheckModelTfLit(Node lit)
{
  Trace("nl-ext-tf-check-model-simple") << "simple check-model for " << lit
                                        << "..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  bool pol = lit.getKind() != kind::NOT;
  Node atom = lit.getKind() == kind::NOT ? lit[0] : lit;

  if (atom.getKind() == kind::GEQ)
  {
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(atom, msum))
    {
      // map from transcendental functions to whether they were set to lower
      // bound
      std::map<Node, bool> set_bound;
      std::vector<Node> sum_bound;
      for (std::pair<const Node, Node>& m : msum)
      {
        Node v = m.first;
        if (v.isNull())
        {
          sum_bound.push_back(m.second.isNull() ? d_one : m.second);
        }
        else
        {
          std::map<Node, std::pair<Node, Node> >::iterator bit =
              d_tf_check_model_bounds.find(v);
          if (bit != d_tf_check_model_bounds.end())
          {
            bool set_lower =
                (m.second.isNull() || m.second.getConst<Rational>().sgn() == 1)
                == pol;
            std::map<Node, bool>::iterator itsb = set_bound.find(v);
            if (itsb != set_bound.end() && itsb->second != set_lower)
            {
              Trace("nl-ext-tf-check-model-simple")
                  << "  failed due to conflicting bound for " << v << std::endl;
              return false;
            }
            set_bound[v] = set_lower;
            // must over/under approximate
            Node vbound = set_lower ? bit->second.first : bit->second.second;
            sum_bound.push_back(ArithMSum::mkCoeffTerm(m.second, vbound));
          }
          else
          {
            Trace("nl-ext-tf-check-model-simple")
                << "  failed due to unknown bound for " << v << std::endl;
            return false;
          }
        }
      }
      Node bound;
      if (sum_bound.size() > 1)
      {
        bound = nm->mkNode(kind::PLUS, sum_bound);
      }
      else if (sum_bound.size() == 1)
      {
        bound = sum_bound[0];
      }
      else
      {
        bound = d_zero;
      }
      Node comp = nm->mkNode(kind::GEQ, bound, d_zero);
      if (!pol)
      {
        comp = comp.negate();
      }
      Trace("nl-ext-tf-check-model-simple") << "  comparison is : " << comp
                                            << std::endl;
      comp = Rewriter::rewrite(comp);
      Assert(comp.isConst());
      Trace("nl-ext-tf-check-model-simple") << "  returned : " << comp
                                            << std::endl;
      return comp == d_true;
    }
  }
  Trace("nl-ext-tf-check-model-simple") << "  failed due to unknown literal."
                                        << std::endl;
  return false;
}

std::vector<Node> NonlinearExtension::checkSplitZero() {
  std::vector<Node> lemmas;
  for (unsigned i = 0; i < d_ms_vars.size(); i++) {
    Node v = d_ms_vars[i];
    if (d_zero_split.insert(v)) {
      Node eq = v.eqNode(d_zero);
      Node literal = d_containing.getValuation().ensureLiteral(eq);
      d_containing.getOutputChannel().requirePhase(literal, true);
      lemmas.push_back(literal.orNode(literal.negate()));
    }
  }
  return lemmas;
}

int NonlinearExtension::checkLastCall(const std::vector<Node>& assertions,
                                      const std::vector<Node>& false_asserts,
                                      const std::vector<Node>& xts)
{
  d_ms_vars.clear();
  d_ms_proc.clear();
  d_ms.clear();
  d_mterms.clear();
  d_m_nconst_factor.clear();
  d_tplane_refine_dir.clear();
  d_ci.clear();
  d_ci_exp.clear();
  d_ci_max.clear();
  d_tf_rep_map.clear();
  d_tf_region.clear();
  d_tf_check_model_bounds.clear();

  int lemmas_proc = 0;
  std::vector<Node> lemmas;
  NodeManager* nm = NodeManager::currentNM();

  Trace("nl-ext-mv") << "Extended terms : " << std::endl;
  // register the extended function terms
  std::map< Node, Node > mvarg_to_term;
  std::vector<Node> trig_no_base;
  for( unsigned i=0; i<xts.size(); i++ ){
    Node a = xts[i];
    computeModelValue(a, 0);
    computeModelValue(a, 1);
    Trace("nl-ext-mv") << "  " << a << " -> " << d_mv[1][a] << " [actual: "
                       << d_mv[0][a] << " ]" << std::endl;
    //Assert(d_mv[1][a].isConst());
    //Assert(d_mv[0][a].isConst());

    if (a.getKind() == NONLINEAR_MULT)
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
        Node mvk = computeModelValue( itvl->second[k], 1 );
        if( !mvk.isConst() ){
          d_m_nconst_factor[a] = true;
        }
      }
      /*
      //mark processed if has a "one" factor (will look at reduced monomial)
      std::map< Node, std::map< Node, unsigned > >::iterator itme =
      d_m_exp.find( a ); Assert( itme!=d_m_exp.end() ); for( std::map< Node,
      unsigned >::iterator itme2 = itme->second.begin(); itme2 !=
      itme->second.end(); ++itme2 ){ Node v = itme->first; Assert(
      d_mv[0].find( v )!=d_mv[0].end() ); Node mvv = d_mv[0][ v ]; if(
      mvv==d_one || mvv==d_neg_one ){ ms_proc[ a ] = true;
      Trace("nl-ext-mv")
      << "...mark " << a << " reduced since has 1 factor." << std::endl;
          break;
        }
      }
      */
    }else if( a.getNumChildren()==1 ){
      bool consider = true;
      // get shifted version
      if (a.getKind() == SINE)
      {
        if( d_trig_is_base.find( a )==d_trig_is_base.end() ){
          consider = false;
          trig_no_base.push_back(a);
          if (d_pi.isNull())
          {
            mkPi();
            getCurrentPiBounds(lemmas);
          }
        }
      }
      if( consider ){
        Node r = d_containing.getValuation().getModel()->getRepresentative(a[0]);
        std::map< Node, Node >::iterator itrm = d_tf_rep_map[a.getKind()].find( r );
        if( itrm!=d_tf_rep_map[a.getKind()].end() ){
          //verify they have the same model value
          if( d_mv[1][a]!=d_mv[1][itrm->second] ){
            // if not, add congruence lemma
            Node cong_lemma = nm->mkNode(
                IMPLIES, a[0].eqNode(itrm->second[0]), a.eqNode(itrm->second));
            lemmas.push_back( cong_lemma );
            //Assert( false );
          }
        }else{
          d_tf_rep_map[a.getKind()][r] = a;
        }
      }
    }
    else if (a.getKind() == PI)
    {
      //TODO?
    }else{
      Assert( false );
    }
  }
  
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas during registration." << std::endl;
    return lemmas_proc;
  }

  // process SINE phase shifting
  for (const Node& a : trig_no_base)
  {
    if (d_trig_base.find(a) == d_trig_base.end())
    {
      Node y =
          nm->mkSkolem("y", nm->realType(), "phase shifted trigonometric arg");
      Node new_a = nm->mkNode(a.getKind(), y);
      d_trig_is_base[new_a] = true;
      d_trig_base[a] = new_a;
      Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a
                         << std::endl;
      Assert(!d_pi.isNull());
      Node shift = nm->mkSkolem("s", nm->integerType(), "number of shifts");
      // FIXME : do not introduce shift here, instead needs model-based
      // refinement for constant shifts (#1284)
      Node shift_lem = nm->mkNode(
          AND,
          mkValidPhase(y, d_pi),
          a[0].eqNode(nm->mkNode(
              PLUS,
              y,
              nm->mkNode(MULT, nm->mkConst(Rational(2)), shift, d_pi))),
          // particular case of above for shift=0
          nm->mkNode(IMPLIES, mkValidPhase(a[0], d_pi), a[0].eqNode(y)),
          new_a.eqNode(a));
      // must do preprocess on this one
      Trace("nl-ext-lemma")
          << "NonlinearExtension::Lemma : shift : " << shift_lem << std::endl;
      d_containing.getOutputChannel().lemma(shift_lem, false, true);
      lemmas_proc++;
    }
  }
  if (lemmas_proc > 0)
  {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc
                    << " new lemmas SINE phase shifting." << std::endl;
    return lemmas_proc;
  }

  // register constants
  registerMonomial(d_one);
  for (unsigned j = 0; j < d_order_points.size(); j++) {
    Node c = d_order_points[j];
    computeModelValue(c, 0);
    computeModelValue(c, 1);
  }

  // register variables
  Trace("nl-ext-mv") << "Variables in monomials : " << std::endl;
  for (unsigned i = 0; i < d_ms_vars.size(); i++) {
    Node v = d_ms_vars[i];
    registerMonomial(v);
    computeModelValue(v, 0);
    computeModelValue(v, 1);
    Trace("nl-ext-mv") << "  " << v << " -> " << d_mv[1][v] << " [actual: " << d_mv[0][v] << " ]" << std::endl;
  }

  //----------------------------------- possibly split on zero
  if (options::nlExtSplitZero()) {
    Trace("nl-ext") << "Get zero split lemmas..." << std::endl;
    lemmas = checkSplitZero();
    lemmas_proc = flushLemmas(lemmas);
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
      return lemmas_proc;
    }
  }

  //-----------------------------------initial lemmas for transcendental functions
  lemmas = checkTranscendentalInitialRefine();
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
    return lemmas_proc;
  }
  
  //-----------------------------------lemmas based on sign (comparison to zero)
  lemmas = checkMonomialSign();
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
    return lemmas_proc;
  }
  
  //-----------------------------------monotonicity of transdental functions
  lemmas = checkTranscendentalMonotonic();
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
    return lemmas_proc;
  }

  //-----------------------------------lemmas based on magnitude of non-zero monomials
  Trace("nl-ext-proc") << "Assign order ids..." << std::endl;
  unsigned r = 3;
  assignOrderIds(d_ms_vars, d_order_vars, r);

  // sort individual variable lists
  Trace("nl-ext-proc") << "Assign order var lists..." << std::endl;
  SortNonlinearExtension smv;
  smv.d_nla = this;
  smv.d_order_type = r;
  smv.d_reverse_order = true;
  for (unsigned j = 0; j < d_ms.size(); j++) {
    std::sort(d_m_vlist[d_ms[j]].begin(), d_m_vlist[d_ms[j]].end(), smv);
  }
  for (unsigned c = 0; c < 3; c++) {
    // c is effort level
    lemmas = checkMonomialMagnitude( c );
    lemmas_proc = flushLemmas(lemmas);
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc
                      << " new lemmas (out of possible " << lemmas.size()
                      << ")." << std::endl;
      return lemmas_proc;
    }
  }

  // sort monomials by degree
  Trace("nl-ext-proc") << "Sort monomials by degree..." << std::endl;
  SortNonlinearExtension snlad;
  snlad.d_nla = this;
  snlad.d_order_type = 4;
  snlad.d_reverse_order = false;
  std::sort(d_ms.begin(), d_ms.end(), snlad);
  // all monomials
  d_mterms.insert(d_mterms.end(), d_ms_vars.begin(), d_ms_vars.end());
  d_mterms.insert(d_mterms.end(), d_ms.begin(), d_ms.end());

  //-----------------------------------inferred bounds lemmas
  //  e.g. x >= t => y*x >= y*t
  std::vector< Node > nt_lemmas;
  lemmas = checkMonomialInferBounds( nt_lemmas, false_asserts );
  // Trace("nl-ext") << "Bound lemmas : " << lemmas.size() << ", " <<
  // nt_lemmas.size() << std::endl;  prioritize lemmas that do not
  // introduce new monomials
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas."
                    << std::endl;
    return lemmas_proc;
  }
  
  // from inferred bound inferences : now do ones that introduce new terms
  lemmas_proc = flushLemmas(nt_lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc
                    << " new (monomial-introducing) lemmas." << std::endl;
    return lemmas_proc;
  }
  
  //------------------------------------factoring lemmas
  //   x*y + x*z >= t => exists k. k = y + z ^ x*k >= t
  if( options::nlExtFactor() ){
    lemmas = checkFactoring( false_asserts );
    lemmas_proc = flushLemmas(lemmas);
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
      return lemmas_proc;
    }
  }

  //------------------------------------resolution bound inferences
  //  e.g. ( y>=0 ^ s <= x*z ^ x*y <= t ) => y*s <= z*t
  if (options::nlExtResBound()) {
    lemmas = checkMonomialInferResBounds();
    lemmas_proc = flushLemmas(lemmas);
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
      return lemmas_proc;
    }
  }
  
  //------------------------------------tangent planes
  if (options::nlExtTangentPlanes() || options::nlExtTfTangentPlanes())
  {
    lemmas_proc = 0;
    if (options::nlExtTangentPlanes())
    {
      lemmas = checkTangentPlanes();
      lemmas_proc += flushLemmas(lemmas);
    }
    if (options::nlExtTfTangentPlanes())
    {
      lemmas = checkTranscendentalTangentPlanes();
      lemmas_proc += flushLemmas(lemmas);
    }
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
      return lemmas_proc;
    }
  }

  return 0;
}

void NonlinearExtension::check(Theory::Effort e) {
  Trace("nl-ext") << std::endl;
  Trace("nl-ext") << "NonlinearExtension::check, effort = " << e << std::endl;
  if (e == Theory::EFFORT_FULL) {
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
  } else {
    bool needsRecheck;
    do
    {
      needsRecheck = false;
      Assert(e == Theory::EFFORT_LAST_CALL);
      Trace("nl-ext-mv") << "Getting model values... check for [model-false]"
                         << std::endl;
      // reset cached information
      d_mv[0].clear();
      d_mv[1].clear();

      // get the assertions
      std::vector<Node> assertions;
      for (Theory::assertions_iterator it = d_containing.facts_begin();
           it != d_containing.facts_end();
           ++it)
      {
        const Assertion& assertion = *it;
        assertions.push_back(assertion.assertion);
      }
      // get the assertions that are false in the model
      const std::vector<Node> false_asserts = checkModel(assertions);

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
      for (context::CDList<TNode>::const_iterator its =
               d_containing.shared_terms_begin();
           its != d_containing.shared_terms_end();
           ++its)
      {
        TNode shared_term = *its;
        // compute its value in the model, and its evaluation in the model
        Node stv0 = computeModelValue(shared_term, 0);
        Node stv1 = computeModelValue(shared_term, 1);
        if (stv0 != stv1)
        {
          num_shared_wrong_value++;
          Trace("nl-ext-mv") << "Bad shared term value : " << shared_term
                             << " : " << stv1 << ", actual is " << stv0
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
            // have no reference
            //   point to rule out the current model.  In this case, we may set
            //   incomplete below.
          }
        }
      }
      Trace("nl-ext-debug") << "     " << num_shared_wrong_value
                            << " shared terms with wrong model value."
                            << std::endl;

      // we require a check either if an assertion is false or a shared term has
      // a wrong value
      bool isIncomplete = false;
      int num_added_lemmas = 0;
      if (!false_asserts.empty() || num_shared_wrong_value > 0)
      {
        isIncomplete = true;
        num_added_lemmas = checkLastCall(assertions, false_asserts, xts);
      }

      // if we did not add a lemma during check
      if(num_added_lemmas==0) {
        if (num_shared_wrong_value > 0)
        {
          // resort to splitting on shared terms with their model value
          isIncomplete = true;
          if (!shared_term_value_splits.empty())
          {
            std::vector<Node> shared_term_value_lemmas;
            for (const Node& eq : shared_term_value_splits)
            {
              Node literal = d_containing.getValuation().ensureLiteral(eq);
              d_containing.getOutputChannel().requirePhase(literal, true);
              shared_term_value_lemmas.push_back(
                  literal.orNode(literal.negate()));
            }
            num_added_lemmas = flushLemmas(shared_term_value_lemmas);
            Trace("nl-ext") << "...added " << num_added_lemmas
                            << " shared term value split lemmas." << std::endl;
          }
          else
          {
            // this can happen if we are trying to do theory combination with
            // trancendental functions
            // since their model value cannot even be computed exactly
          }
        }
        if (num_added_lemmas == 0)
        {
          if (isIncomplete)
          {
            // check the model using error bounds on the Taylor approximation
            if (!d_tf_rep_map.empty() && checkModelTf(false_asserts))
            {
              isIncomplete = false;
            }
          }
          if (isIncomplete)
          {
            if (options::nlExtTfIncPrecision() && !d_tf_rep_map.empty())
            {
              d_taylor_degree++;
              d_secant_points.clear();
              needsRecheck = true;
              // increase precision for PI?
              // Difficult since Taylor series is very slow to converge
              Trace("nl-ext") << "...increment Taylor degree to "
                              << d_taylor_degree << std::endl;
            }
            else
            {
              Trace("nl-ext") << "...failed to send lemma in "
                                 "NonLinearExtension, set incomplete"
                              << std::endl;
              d_containing.getOutputChannel().setIncomplete();
            }
          }
        }
      }
    } while (needsRecheck);
  }
}

void NonlinearExtension::addDefinition(Node lem)
{
  Trace("nl-ext") << "NonlinearExtension::addDefinition : " << lem << std::endl;
  d_def_lemmas.insert(lem);
}

void NonlinearExtension::presolve()
{
  Trace("nl-ext") << "NonlinearExtension::presolve, #defs = "
                  << d_def_lemmas.size() << std::endl;
  for (NodeSet::const_iterator it = d_def_lemmas.begin();
       it != d_def_lemmas.end();
       ++it)
  {
    flushLemma(*it);
  }
}

void NonlinearExtension::assignOrderIds(std::vector<Node>& vars,
                                        NodeMultiset& order,
                                        unsigned orderType) {
  SortNonlinearExtension smv;
  smv.d_nla = this;
  smv.d_order_type = orderType;
  smv.d_reverse_order = false;
  std::sort(vars.begin(), vars.end(), smv);

  order.clear();
  // assign ordering id's
  unsigned counter = 0;
  unsigned order_index = (orderType == 0 || orderType == 2) ? 0 : 1;
  Node prev;
  for (unsigned j = 0; j < vars.size(); j++) {
    Node x = vars[j];
    Node v = get_compare_value(x, orderType);
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
          Node vv = get_compare_value(d_order_points[order_index], orderType);
          if (compare_value(v, vv, orderType) <= 0) {
            counter++;
            Trace("nl-ext-mvo")
                << "O_" << orderType << "[" << d_order_points[order_index]
                << "] = " << counter << std::endl;
            order[d_order_points[order_index]] = counter;
            prev = vv;
            order_index++;
            success = true;
          }
        }
      } while (success);
    }
    if (prev.isNull() || compare_value(v, prev, orderType) != 0) {
      counter++;
    }
    Trace("nl-ext-mvo") << "O_" << orderType << "[" << x << "] = " << counter
                        << std::endl;
    order[x] = counter;
    prev = v;
  }
  while (order_index < d_order_points.size()) {
    counter++;
    Trace("nl-ext-mvo") << "O_" << orderType << "["
                        << d_order_points[order_index] << "] = " << counter
                        << std::endl;
    order[d_order_points[order_index]] = counter;
    order_index++;
  }
}

int NonlinearExtension::compare(Node i, Node j, unsigned orderType) const {
  Assert(orderType >= 0);
  if (orderType <= 3) {
    Node ci = get_compare_value(i, orderType);
    Node cj = get_compare_value(j, orderType);
    if( ci.isConst() ){
      if( cj.isConst() ){
        return compare_value(ci, cj, orderType);
      }else{
        return 1; 
      }
    }else{
      if( cj.isConst() ){
        return -1;
      }else{
        return 0;
      }
    }
    // minimal degree
  } else if (orderType == 4) {
    unsigned i_count = getCount(d_m_degree, i);
    unsigned j_count = getCount(d_m_degree, j);
    return i_count == j_count ? 0 : (i_count < j_count ? 1 : -1);
  } else {
    return 0;
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
    d_pi_bound[0] = NodeManager::currentNM()->mkConst( Rational(333)/Rational(106) );
    d_pi_bound[1] = NodeManager::currentNM()->mkConst( Rational(355)/Rational(113) );
  }
}

void NonlinearExtension::getCurrentPiBounds( std::vector< Node >& lemmas ) {
  Node pi_lem = NodeManager::currentNM()->mkNode(
      AND,
      NodeManager::currentNM()->mkNode(GEQ, d_pi, d_pi_bound[0]),
      NodeManager::currentNM()->mkNode(LEQ, d_pi, d_pi_bound[1]));
  lemmas.push_back( pi_lem );
}

int NonlinearExtension::compare_value(Node i, Node j,
                                      unsigned orderType) const {
  Assert(orderType >= 0 && orderType <= 3);
  Assert( i.isConst() && j.isConst() );
  Trace("nl-ext-debug") << "compare value " << i << " " << j
                        << ", o = " << orderType << std::endl;
  int ret;
  if (i == j) {
    ret = 0;
  } else if (orderType == 0 || orderType == 2) {
    ret = i.getConst<Rational>() < j.getConst<Rational>() ? 1 : -1;
  } else {
    Trace("nl-ext-debug") << "vals : " << i.getConst<Rational>() << " "
                          << j.getConst<Rational>() << std::endl;
    Trace("nl-ext-debug") << i.getConst<Rational>().abs() << " "
                          << j.getConst<Rational>().abs() << std::endl;
    ret = (i.getConst<Rational>().abs() == j.getConst<Rational>().abs()
               ? 0
               : (i.getConst<Rational>().abs() < j.getConst<Rational>().abs()
                      ? 1
                      : -1));
  }
  Trace("nl-ext-debug") << "...return " << ret << std::endl;
  return ret;
}

Node NonlinearExtension::get_compare_value(Node i, unsigned orderType) const {
  if (i.isConst())
  {
    return i;
  }
  Trace("nl-ext-debug") << "Compare variable " << i << " " << orderType
                        << std::endl;
  Assert(orderType >= 0 && orderType <= 3);
  unsigned mindex = orderType <= 1 ? 0 : 1;
  std::map<Node, Node>::const_iterator iti = d_mv[mindex].find(i);
  Assert(iti != d_mv[mindex].end());
  return iti->second;
}

// show a <> 0 by inequalities between variables in monomial a w.r.t 0
int NonlinearExtension::compareSign(Node oa, Node a, unsigned a_index,
                                    int status, std::vector<Node>& exp,
                                    std::vector<Node>& lem) {
  Trace("nl-ext-debug") << "Process " << a << " at index " << a_index
                        << ", status is " << status << std::endl;
  Assert(d_mv[1].find(oa) != d_mv[1].end());
  if (a_index == d_m_vlist[a].size()) {
    if (d_mv[1][oa].getConst<Rational>().sgn() != status) {
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
    Assert( d_mv[1].find(av) != d_mv[0].end() );
    Assert( d_mv[1][av].isConst() );
    int sgn = d_mv[1][av].getConst<Rational>().sgn();
    Trace("nl-ext-debug") << "Process var " << av << "^" << aexp
                          << ", model sign = " << sgn << std::endl;
    if (sgn == 0) {
      if (d_mv[1][oa].getConst<Rational>().sgn() != 0) {
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
    // finished, compare abstract values
    int modelStatus = compare(oa, ob, 3) * -2;
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
          IMPLIES, safeConstructNary(AND, exp), mkLit(oa, ob, status, 1));
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
        exp.push_back(mkLit(d_one, bv, bvo == ovo ? 0 : 2, 1));
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
        exp.push_back(mkLit(av, d_one, avo == ovo ? 0 : 2, 1));
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
          exp.push_back(mkLit(av, d_one, avo == ovo ? 0 : 2, 1));
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
          exp.push_back(mkLit(av, bv, avo == bvo ? 0 : 2, 1));
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
          exp.push_back(mkLit(d_one, bv, bvo == ovo ? 0 : 2, 1));
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
      Trace("nl-ext-debug") << "  process " << a << ", mv=" << d_mv[0][a] << "..." << std::endl;
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
            Assert( d_mv[0].find( v )!=d_mv[0].end() );
            if( d_mv[0][v].isConst() ){
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
  Trace("nl-ext-comp") << "Compute redundand_cies for " << lemmas.size()
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
  unsigned kstart = d_ms_vars.size();
  for (unsigned k = kstart; k < d_mterms.size(); k++) {
    Node t = d_mterms[k];
    // if this term requires a refinement
    if (d_tplane_refine_dir.find(t) != d_tplane_refine_dir.end()) {
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
              Node a_v_c = computeModelValue(a, 1);
              Node b_v_c = computeModelValue(b, 1);
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
                  Assert( !pt_v.isNull() );
                  if( curr_v!=pt_v ){
                    Node do_extend = NodeManager::currentNM()->mkNode( ( p==1 || p==3 ) ? GT : LT, curr_v, pt_v );
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
                Node tplane = NodeManager::currentNM()->mkNode(
                    MINUS,
                    NodeManager::currentNM()->mkNode(
                        PLUS,
                        NodeManager::currentNM()->mkNode(MULT, b_v, a),
                        NodeManager::currentNM()->mkNode(MULT, a_v, b)),
                    NodeManager::currentNM()->mkNode(MULT, a_v, b_v));
                for (unsigned d = 0; d < 4; d++) {
                  Node aa = NodeManager::currentNM()->mkNode(
                      d == 0 || d == 3 ? GEQ : LEQ, a, a_v);
                  Node ab = NodeManager::currentNM()->mkNode(
                      d == 1 || d == 3 ? GEQ : LEQ, b, b_v);
                  Node conc = NodeManager::currentNM()->mkNode(
                      d <= 1 ? LEQ : GEQ, t, tplane);
                  Node tlem = NodeManager::currentNM()->mkNode(
                      OR, aa.negate(), ab.negate(), conc);
                  Trace("nl-ext-tplanes")
                      << "Tangent plane lemma : " << tlem << std::endl;
                  lemmas.push_back(tlem);
                }
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
    std::vector<Node>& nt_lemmas, const std::vector<Node>& false_asserts)
{
  std::vector< Node > lemmas; 
  // register constraints
  Trace("nl-ext-debug") << "Register bound constraints..." << std::endl;
  for (context::CDList<Assertion>::const_iterator it =
           d_containing.facts_begin();
       it != d_containing.facts_end(); ++it) {
    Node lit = (*it).assertion;
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
            Node query_mv = computeModelValue(query, 1);
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
            Node rhs_v = computeModelValue(rhs, 0);
            Node x_v = computeModelValue(x, 0);
            if( rhs_v.isConst() && x_v.isConst() ){
              bool needsRefine = false;
              bool refineDir;
              if (rhs_v == x_v) {
                if (type == GT)
                {
                  needsRefine = true;
                  refineDir = true;
                }
                else if (type == LT)
                {
                  needsRefine = true;
                  refineDir = false;
                }
              } else if (x_v.getConst<Rational>() > rhs_v.getConst<Rational>()) {
                if (type != GT && type != GEQ)
                {
                  needsRefine = true;
                  refineDir = false;
                }
              } else {
                if (type != LT && type != LEQ)
                {
                  needsRefine = true;
                  refineDir = true;
                }
              }
              Trace("nl-ext-tplanes-cons-debug")
                  << "...compute if bound corresponds to a required "
                     "refinement"
                  << std::endl;
              Trace("nl-ext-tplanes-cons-debug")
                  << "...M[" << x << "] = " << x_v << ", M[" << rhs
                  << "] = " << rhs_v << std::endl;
              Trace("nl-ext-tplanes-cons-debug") << "...refine = " << needsRefine
                                                 << "/" << refineDir << std::endl;
              if (needsRefine) {
                Trace("nl-ext-tplanes-cons")
                    << "---> By " << lit << " and since M[" << x << "] = " << x_v
                    << ", M[" << rhs << "] = " << rhs_v << ", ";
                Trace("nl-ext-tplanes-cons")
                    << "monomial " << x << " should be "
                    << (refineDir ? "larger" : "smaller") << std::endl;
                d_tplane_refine_dir[x][refineDir] = true;
              }
            }
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
                Assert(d_m_contain_mult[x].find(y) !=
                       d_m_contain_mult[x].end());
                Node mult = d_m_contain_mult[x][y];
                // x <k> t => m*x <k'> t  where y = m*x
                // get the sign of mult
                Node mmv = computeModelValue(mult);
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
                    Node infer_mv = computeModelValue(infer, 1);
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
    const std::vector<Node>& false_asserts)
{
  std::vector< Node > lemmas; 
  Trace("nl-ext") << "Get factoring lemmas..." << std::endl;
  for (context::CDList<Assertion>::const_iterator it =
           d_containing.facts_begin();
       it != d_containing.facts_end(); ++it) {
    Node lit = (*it).assertion;
    bool polarity = lit.getKind() != NOT;
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    if (std::find(false_asserts.begin(), false_asserts.end(), lit)
            != false_asserts.end()
        || d_skolem_atoms.find(atom) != d_skolem_atoms.end())
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
            } /* else{
              factor_to_mono[itm->first].push_back( itm->second.isNull() ? d_one : itm->second );
              factor_to_mono_orig[itm->first].push_back( itm->first );
            }*/
          }
        }
        for( std::map< Node, std::vector< Node > >::iterator itf = factor_to_mono.begin(); itf != factor_to_mono.end(); ++itf ){
          if( itf->second.size()>1 ){
            Node sum = NodeManager::currentNM()->mkNode(PLUS, itf->second);
            sum = Rewriter::rewrite( sum );
            Trace("nl-ext-factor") << "* Factored sum for " << itf->first << " : " << sum << std::endl;
            Node kf = getFactorSkolem( sum, lemmas ); 
            std::vector< Node > poly;
            poly.push_back(
                NodeManager::currentNM()->mkNode(MULT, itf->first, kf));
            std::map< Node, std::vector< Node > >::iterator itfo = factor_to_mono_orig.find( itf->first );
            Assert( itfo!=factor_to_mono_orig.end() );
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
            d_skolem_atoms.insert( conc_lit );
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
    d_skolem_atoms.insert( k_eq );
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
            std::map<Node, Node>::iterator itb = d_mono_diff[b].find(a);
            Assert(itb != d_mono_diff[b].end());
            Node mv_a = computeModelValue(ita->second, 1);
            Assert(mv_a.isConst());
            int mv_a_sgn = mv_a.getConst<Rational>().sgn();
            Assert(mv_a_sgn != 0);
            Node mv_b = computeModelValue(itb->second, 1);
            Assert(mv_b.isConst());
            int mv_b_sgn = mv_b.getConst<Rational>().sgn();
            Assert(mv_b_sgn != 0);
            Trace("nl-ext-rbound") << "Get resolution inferences for [a] "
                                   << a << " vs [b] " << b << std::endl;
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
                          Node conc_mv = computeModelValue(conc, 1);
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
  for( std::map< Kind, std::map< Node, Node > >::iterator it = d_tf_rep_map.begin(); it != d_tf_rep_map.end(); ++it ){
    for( std::map< Node, Node >::iterator itt = it->second.begin(); itt != it->second.end(); ++itt ){
      Node t = itt->second;
      Assert( d_mv[1].find( t )!=d_mv[1].end() );
      //initial refinements
      if( d_tf_initial_refine.find( t )==d_tf_initial_refine.end() ){
        d_tf_initial_refine[t] = true;
        Node lem;
        if (it->first == SINE)
        {
          Node symn = NodeManager::currentNM()->mkNode(
              SINE, NodeManager::currentNM()->mkNode(MULT, d_neg_one, t[0]));
          symn = Rewriter::rewrite( symn );
          //can assume its basis since phase is split over 0
          d_trig_is_base[symn] = true;
          Assert( d_trig_is_base.find( t ) != d_trig_is_base.end() );
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
        else if (it->first == EXPONENTIAL)
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
  
  for( std::map< Kind, std::map< Node, Node > >::iterator it = d_tf_rep_map.begin(); it != d_tf_rep_map.end(); ++it ){
    for( std::map< Node, Node >::iterator itt = it->second.begin(); itt != it->second.end(); ++itt ){
      computeModelValue( itt->second[0], 1 );
      Assert( d_mv[1].find( itt->second[0] )!=d_mv[1].end() );
      if( d_mv[1][itt->second[0]].isConst() ){
        Trace("nl-ext-tf-mono-debug") << "...tf term : " << itt->second[0] << std::endl;
        sorted_tf_args[ it->first ].push_back( itt->second[0] );
        tf_arg_to_term[ it->first ][ itt->second[0] ] = itt->second;
      }
    } 
  }
  
  SortNonlinearExtension smv;
  smv.d_nla = this;
  //sort by concrete values
  smv.d_order_type = 0;
  smv.d_reverse_order = true;
  for( std::map< Kind, std::map< Node, Node > >::iterator it = d_tf_rep_map.begin(); it != d_tf_rep_map.end(); ++it ){
    Kind k = it->first;
    if( !sorted_tf_args[k].empty() ){
      std::sort( sorted_tf_args[k].begin(), sorted_tf_args[k].end(), smv );
      Trace("nl-ext-tf-mono") << "Sorted transcendental function list for " << k << " : " << std::endl;
      for( unsigned i=0; i<sorted_tf_args[it->first].size(); i++ ){
        Node targ = sorted_tf_args[k][i];
        Assert( d_mv[1].find( targ )!=d_mv[1].end() );
        Trace("nl-ext-tf-mono") << "  " << targ << " -> " << d_mv[1][targ] << std::endl;
        Node t = tf_arg_to_term[k][targ];
        Assert( d_mv[1].find( t )!=d_mv[1].end() );
        Trace("nl-ext-tf-mono") << "     f-val : " << d_mv[1][t] << std::endl;
      }
      std::vector< Node > mpoints;
      std::vector< Node > mpoints_vals;
      if (it->first == SINE)
      {
        mpoints.push_back( d_pi );
        mpoints.push_back( d_pi_2 );
        mpoints.push_back(d_zero);
        mpoints.push_back( d_pi_neg_2 );
        mpoints.push_back( d_pi_neg );
      }
      else if (it->first == EXPONENTIAL)
      {
        mpoints.push_back( Node::null() );
      }
      if( !mpoints.empty() ){
        //get model values for points
        for( unsigned i=0; i<mpoints.size(); i++ ){
          Node mpv;
          if( !mpoints[i].isNull() ){
            mpv = computeModelValue( mpoints[i], 1 );
            Assert( mpv.isConst() );
          }
          mpoints_vals.push_back( mpv );
        }
        
        unsigned mdir_index = 0;
        int monotonic_dir = -1;
        Node mono_bounds[2];
        Node targ, targval, t, tval;
        for( unsigned i=0; i<sorted_tf_args[it->first].size(); i++ ){
          Node sarg = sorted_tf_args[k][i];
          Assert( d_mv[1].find( sarg )!=d_mv[1].end() );
          Node sargval = d_mv[1][sarg];
          Assert( sargval.isConst() ); 
          Node s = tf_arg_to_term[k][ sarg ];
          Assert( d_mv[1].find( s )!=d_mv[1].end() );
          Node sval = d_mv[1][s];
          Assert( sval.isConst() ); 
        
          //increment to the proper monotonicity region
          bool increment = true;
          while (increment && mdir_index < mpoints.size())
          {
            increment = false;
            if( mpoints[mdir_index].isNull() ){
              increment = true;
            }else{
              Node pval = mpoints_vals[mdir_index];
              Assert( pval.isConst() );
              if( sargval.getConst<Rational>() < pval.getConst<Rational>() ){
                increment = true;
                Trace("nl-ext-tf-mono") << "...increment at " << sarg << " since model value is less than " << mpoints[mdir_index] << std::endl;
              }
            }
            if( increment ){
              tval = Node::null();
              mono_bounds[1] = mpoints[mdir_index];
              mdir_index++;
              monotonic_dir = regionToMonotonicityDir(it->first, mdir_index);
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
                Assert( !mono_bounds[1].isNull() );
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

std::vector<Node> NonlinearExtension::checkTranscendentalTangentPlanes()
{
  std::vector<Node> lemmas;
  Trace("nl-ext") << "Get tangent plane lemmas for transcendental functions..."
                  << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  // this implements Figure 3 of "Satisfiaility Modulo Transcendental Functions
  // via Incremental Linearization" by Cimatti et al
  for (std::pair<const Kind, std::map<Node, Node> >& tfs : d_tf_rep_map)
  {
    Kind k = tfs.first;
    Node tft = nm->mkNode(k, d_zero);
    Trace("nl-ext-tf-tplanes-debug") << "Taylor variables: " << std::endl;
    Trace("nl-ext-tf-tplanes-debug")
        << "          taylor_real_fv : " << d_taylor_real_fv << std::endl;
    Trace("nl-ext-tf-tplanes-debug")
        << "     taylor_real_fv_base : " << d_taylor_real_fv_base << std::endl;
    Trace("nl-ext-tf-tplanes-debug")
        << " taylor_real_fv_base_rem : " << d_taylor_real_fv_base_rem
        << std::endl;
    Trace("nl-ext-tf-tplanes-debug") << std::endl;

    // we substitute into the Taylor sum P_{n,f(0)}( x )
    std::vector<Node> taylor_vars;
    taylor_vars.push_back(d_taylor_real_fv);

    // Figure 3: P_l, P_u
    // mapped to for signs of c
    std::map<int, Node> poly_approx_bounds[2];
    // n is the Taylor degree we are currently considering
    unsigned n = 2 * d_taylor_degree;
    // n must be even
    std::pair<Node, Node> taylor = getTaylor(tft, n);
    Trace("nl-ext-tf-tplanes-debug") << "Taylor for " << k
                                     << " is : " << taylor.first << std::endl;
    Node taylor_sum = Rewriter::rewrite(taylor.first);
    Trace("nl-ext-tf-tplanes-debug") << "Taylor for " << k
                                     << " is (post-rewrite) : " << taylor_sum
                                     << std::endl;
    Assert(taylor.second.getKind() == MULT);
    Assert(taylor.second.getNumChildren() == 2);
    Assert(taylor.second[0].getKind() == DIVISION);
    Trace("nl-ext-tf-tplanes-debug") << "Taylor remainder for " << k << " is "
                                     << taylor.second << std::endl;
    // ru is x^{n+1}/(n+1)!
    Node ru = nm->mkNode(DIVISION, taylor.second[1], taylor.second[0][1]);
    ru = Rewriter::rewrite(ru);
    Trace("nl-ext-tf-tplanes-debug")
        << "Taylor remainder factor is (post-rewrite) : " << ru << std::endl;
    if (k == EXPONENTIAL)
    {
      poly_approx_bounds[0][1] = taylor_sum;
      poly_approx_bounds[0][-1] = taylor_sum;
      poly_approx_bounds[1][1] = Rewriter::rewrite(
          nm->mkNode(MULT, taylor_sum, nm->mkNode(PLUS, d_one, ru)));
      poly_approx_bounds[1][-1] =
          Rewriter::rewrite(nm->mkNode(PLUS, taylor_sum, ru));
    }
    else
    {
      Assert(k == SINE);
      poly_approx_bounds[0][1] =
          Rewriter::rewrite(nm->mkNode(MINUS, taylor_sum, ru));
      poly_approx_bounds[0][-1] = poly_approx_bounds[0][1];
      poly_approx_bounds[1][1] =
          Rewriter::rewrite(nm->mkNode(PLUS, taylor_sum, ru));
      poly_approx_bounds[1][-1] = poly_approx_bounds[1][1];
    }
    Trace("nl-ext-tf-tplanes") << "Polynomial approximation for " << k
                               << " is: " << std::endl;
    Trace("nl-ext-tf-tplanes") << " Lower (pos): " << poly_approx_bounds[0][1]
                               << std::endl;
    Trace("nl-ext-tf-tplanes") << " Upper (pos): " << poly_approx_bounds[1][1]
                               << std::endl;
    Trace("nl-ext-tf-tplanes") << " Lower (neg): " << poly_approx_bounds[0][-1]
                               << std::endl;
    Trace("nl-ext-tf-tplanes") << " Upper (neg): " << poly_approx_bounds[1][-1]
                               << std::endl;

    for (std::pair<const Node, Node>& tfr : tfs.second)
    {
      // Figure 3 : tf( x )
      Node tf = tfr.second;

      bool consider = true;
      if (k == SINE)
      {
        // we do not consider e.g. sin( -1*x ), since considering sin( x ) will
        // have the same effect
        consider = tf[0].isVar();
      }
      int csign;
      Node c;
      if (consider)
      {
        // Figure 3 : c
        c = computeModelValue(tf[0], 1);
        Assert(c.isConst());
        csign = c.getConst<Rational>().sgn();
        consider = csign != 0;
      }

      if (consider)
      {
        Assert(csign == 1 || csign == -1);

        // Figure 3 : v
        Node v = computeModelValue(tf, 1);

        // check value of tf
        Trace("nl-ext-tf-tplanes") << "Process tangent plane refinement for "
                                   << tf << "..." << std::endl;
        Trace("nl-ext-tf-tplanes") << "  value in model : v = " << v
                                   << std::endl;
        Trace("nl-ext-tf-tplanes") << "  arg value in model : c = " << c
                                   << std::endl;

        // compute the concavity
        int region = -1;
        std::unordered_map<Node, int, NodeHashFunction>::iterator itr =
            d_tf_region.find(tf);
        if (itr != d_tf_region.end())
        {
          region = itr->second;
          Trace("nl-ext-tf-tplanes") << "  region is : " << region << std::endl;
        }
        // Figure 3 : conc
        int concavity = regionToConcavity(k, itr->second);
        Trace("nl-ext-tf-tplanes") << "  concavity is : " << concavity
                                   << std::endl;
        if (concavity != 0)
        {
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
          std::map<unsigned, Node> model_values;
          for (unsigned d = 0; d < 2; d++)
          {
            Node pab = poly_approx_bounds[d][csign];
            if (!pab.isNull())
            {
              // { x -> tf[0] }
              std::vector<Node> taylor_subs;
              taylor_subs.push_back(tf[0]);
              Assert(taylor_vars.size() == taylor_subs.size());
              pab = pab.substitute(taylor_vars.begin(),
                                   taylor_vars.end(),
                                   taylor_subs.begin(),
                                   taylor_subs.end());
              pab = Rewriter::rewrite(pab);
              Node v_pab = computeModelValue(pab, 1);
              model_values[d] = v_pab;
              Assert(v_pab.isConst());
              Trace("nl-ext-tf-tplanes-debug") << "...model value of " << pab
                                               << " is " << v_pab << std::endl;
              Node comp = nm->mkNode(d == 0 ? LT : GT, v, v_pab);
              Trace("nl-ext-tf-tplanes-debug") << "...compare : " << comp
                                               << std::endl;
              Node compr = Rewriter::rewrite(comp);
              Trace("nl-ext-tf-tplanes-debug") << "...got : " << compr
                                               << std::endl;
              if (compr == d_true)
              {
                // beyond the bounds
                if (d == 0)
                {
                  poly_approx = poly_approx_bounds[d][csign];
                  is_tangent = concavity == 1;
                  is_secant = concavity == -1;
                }
                else
                {
                  poly_approx = poly_approx_bounds[d][csign];
                  is_tangent = concavity == -1;
                  is_secant = concavity == 1;
                }
                Trace("nl-ext-tf-tplanes") << "*** Outside boundary point (";
                Trace("nl-ext-tf-tplanes") << (d == 0 ? "low" : "high") << ") ";
                Trace("nl-ext-tf-tplanes") << comp << ", will refine..."
                                           << std::endl;
                Trace("nl-ext-tf-tplanes")
                    << "    poly_approx = " << poly_approx << std::endl;
                Trace("nl-ext-tf-tplanes") << "    is_tangent = " << is_tangent
                                           << std::endl;
                Trace("nl-ext-tf-tplanes") << "    is_secant = " << is_secant
                                           << std::endl;
                break;
              }
              else
              {
                Trace("nl-ext-tf-tplanes") << "  ...within "
                                           << (d == 0 ? "low" : "high")
                                           << " bound : ";
                Trace("nl-ext-tf-tplanes") << comp << std::endl;
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
            Trace("nl-ext-tf-tplanes-debug") << "...poly appoximation at c is "
                                             << poly_approx_c << std::endl;
          }
          else
          {
            // store for check model bounds
            Node atf = computeModelValue(tf);
            d_tf_check_model_bounds[atf] =
                std::pair<Node, Node>(model_values[0], model_values[1]);
          }

          if (is_tangent)
          {
            // compute tangent plane
            // Figure 3: T( x )
            Node tplane;
            Node poly_approx_deriv =
                getDerivative(poly_approx, d_taylor_real_fv);
            Assert(!poly_approx_deriv.isNull());
            poly_approx_deriv = Rewriter::rewrite(poly_approx_deriv);
            Trace("nl-ext-tf-tplanes-debug") << "...derivative of "
                                             << poly_approx << " is "
                                             << poly_approx_deriv << std::endl;
            std::vector<Node> taylor_subs;
            taylor_subs.push_back(c);
            Assert(taylor_vars.size() == taylor_subs.size());
            Node poly_approx_c_deriv =
                poly_approx_deriv.substitute(taylor_vars.begin(),
                                             taylor_vars.end(),
                                             taylor_subs.begin(),
                                             taylor_subs.end());
            tplane = nm->mkNode(
                PLUS,
                poly_approx_c,
                nm->mkNode(
                    MULT, poly_approx_c_deriv, nm->mkNode(MINUS, tf[0], c)));

            Node lem = nm->mkNode(concavity == 1 ? GEQ : LEQ, tf, tplane);
            std::vector<Node> antec;
            for (unsigned i = 0; i < 2; i++)
            {
              if (!bounds[i].isNull())
              {
                antec.push_back(
                    nm->mkNode(i == 0 ? GEQ : LEQ, tf[0], bounds[i]));
              }
            }
            if (!antec.empty())
            {
              Node antec_n =
                  antec.size() == 1 ? antec[0] : nm->mkNode(AND, antec);
              lem = nm->mkNode(IMPLIES, antec_n, lem);
            }
            Trace("nl-ext-tf-tplanes-debug")
                << "*** Tangent plane lemma (pre-rewrite): " << lem
                << std::endl;
            lem = Rewriter::rewrite(lem);
            Trace("nl-ext-tf-tplanes") << "*** Tangent plane lemma : " << lem
                                       << std::endl;
            // Figure 3 : line 9
            lemmas.push_back(lem);
          }
          else if (is_secant)
          {
            // bounds are the minimum and maximum previous secant points
            Assert(std::find(d_secant_points[tf].begin(),
                             d_secant_points[tf].end(),
                             c)
                   == d_secant_points[tf].end());
            // insert into the vector
            d_secant_points[tf].push_back(c);
            // sort
            SortNonlinearExtension smv;
            smv.d_nla = this;
            smv.d_order_type = 0;
            std::sort(
                d_secant_points[tf].begin(), d_secant_points[tf].end(), smv);
            // get the resulting index of c
            unsigned index =
                std::find(
                    d_secant_points[tf].begin(), d_secant_points[tf].end(), c)
                - d_secant_points[tf].begin();
            // bounds are the next closest upper/lower bound values
            if (index > 0)
            {
              bounds[0] = d_secant_points[tf][index - 1];
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
            if (index < d_secant_points[tf].size() - 1)
            {
              bounds[1] = d_secant_points[tf][index + 1];
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
            Trace("nl-ext-tf-tplanes-debug")
                << "...secant bounds are : " << bounds[0] << " ... "
                << bounds[1] << std::endl;

            for (unsigned s = 0; s < 2; s++)
            {
              // compute secant plane
              Assert(!poly_approx.isNull());
              Assert(!bounds[s].isNull());
              // take the model value of l or u (since may contain PI)
              Node b = computeModelValue(bounds[s], 1);
              Trace("nl-ext-tf-tplanes-debug") << "...model value of bound "
                                               << bounds[s] << " is " << b
                                               << std::endl;
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
                Trace("nl-ext-tf-tplanes-debug")
                    << "*** Secant plane lemma (pre-rewrite) : " << lem
                    << std::endl;
                lem = Rewriter::rewrite(lem);
                Trace("nl-ext-tf-tplanes") << "*** Secant plane lemma : " << lem
                                           << std::endl;
                // Figure 3 : line 22
                lemmas.push_back(lem);
              }
            }
          }
        }
      }
    }
  }

  return lemmas;
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

std::pair<Node, Node> NonlinearExtension::getTaylor(TNode fa, unsigned n)
{
  Node fac;  // what term we cache for fa
  if (fa[0] == d_zero)
  {
    // optimization : simpler to compute (x-fa[0])^n if we are centered around
    // 0.
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

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
