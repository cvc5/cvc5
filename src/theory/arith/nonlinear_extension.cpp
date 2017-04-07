/*********************                                                        */
/*! \file nl_alg.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_model.h"

using namespace std;
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
  Node t = QuantArith::mkCoeffTerm(coeff, x);
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
      if (current.getKind() == kind::NONLINEAR_MULT) {
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
      d_needsLastCall(false) {
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_order_points.push_back(d_neg_one);
  d_order_points.push_back(d_zero);
  d_order_points.push_back(d_one);
}

NonlinearExtension::~NonlinearExtension() {}

// Returns a reference to either map[key] if it exists in the map
// or to a default value otherwise.
//
// Warning: special care must be taken if value is a temporary object.
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

  Node mult_term = safeConstructNary(kind::MULT, diff_children);
  Node nlmult_term = safeConstructNary(kind::NONLINEAR_MULT, diff_children);
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
          if (QuantArith::getMonomialSum(n, msum)) {
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
              bool success;
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
                  if (!QuantArith::getMonomialSum(ns, msum)) {
                    success = false;
                  }else{
                    d_rep_sum_unique_exp[n] = exp_rm.size()==1 ? exp_rm[0] : NodeManager::currentNM()->mkNode( kind::AND, exp_rm );
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
    expn = r_c_exp.size() == 1
               ? r_c_exp[0]
               : NodeManager::currentNM()->mkNode(kind::AND, r_c_exp);
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
          Node v_c = QuantArith::solveEqualityFor(eq, result.variable_term);
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
        Node v_c = QuantArith::solveEqualityFor(eq, v);
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
    return std::make_pair(n.getKind() != kind::NONLINEAR_MULT, Node::null());
  }
  Assert(n == d_zero);
  Trace("nl-ext-zero-exp") << "Infer zero : " << on << " == " << n << std::endl;
  // minimize explanation
  const std::set<Node> vars(on.begin(), on.end());

  for (unsigned i = 0; i < exp.size(); i++) {
    Trace("nl-ext-zero-exp") << "  exp[" << i << "] = " << exp[i] << std::endl;
    std::vector<Node> eqs;
    if (exp[i].getKind() == kind::EQUAL) {
      eqs.push_back(exp[i]);
    } else if (exp[i].getKind() == kind::AND) {
      for (unsigned j = 0; j < exp[i].getNumChildren(); j++) {
        if (exp[i][j].getKind() == kind::EQUAL) {
          eqs.push_back(exp[i][j]);
        }
      }
    }

    for (unsigned j = 0; j < eqs.size(); j++) {
      for (unsigned r = 0; r < 2; r++) {
        if (eqs[j][r] == d_zero && vars.find(eqs[j][1 - r]) != vars.end()) {
          Trace("nl-ext-zero-exp") << "...single exp : " << eqs[j] << std::endl;
          return std::make_pair(true, eqs[j]);
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
    Trace("nl-ext-debug") << "computeModelValue " << n << std::endl;
    Node ret;
    if (n.isConst()) {
      ret = n;
    } else {
      if (n.getNumChildren() == 0) {
        ret = d_containing.getValuation().getModel()->getValue(n);
      } else {
        if (index == 1 && n.getKind() == kind::NONLINEAR_MULT) {
          if (d_containing.getValuation().getModel()->hasTerm(n)) {
            // use model value for abstraction
            ret = d_containing.getValuation().getModel()->getRepresentative(n);
          } else {
            // abstraction does not exist, use concrete
            ret = computeModelValue(n, 0);
          }
        } else {
          // otherwise, compute true value
          std::vector<Node> children;
          if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
            children.push_back(n.getOperator());
          }
          for (unsigned i = 0; i < n.getNumChildren(); i++) {
            Node mc = computeModelValue(n[i], index);
            children.push_back(mc);
          }
          ret = Rewriter::rewrite(
              NodeManager::currentNM()->mkNode(n.getKind(), children));
          if (!ret.isConst()) {
            Trace("nl-ext-debug") << "...got non-constant : " << ret << " for "
                                  << n << ", ask model directly." << std::endl;
            ret = d_containing.getValuation().getModel()->getValue(ret);
          }
        }
      }
      if (ret.getType().isReal() && !isArithKind(n.getKind())) {
        // Trace("nl-ext-mv-debug") << ( index==0 ? "M" : "M_A" ) << "[ " << n
        // << " ] -> " << ret << std::endl;
        Assert(ret.isConst());
      }
    }
    Trace("nl-ext-debug") << "computed " << (index == 0 ? "M" : "M_A") << "["
                          << n << "] = " << ret << std::endl;
    d_mv[index][n] = ret;
    return ret;
  }
}

void NonlinearExtension::registerMonomial(Node n) {
  if (!IsInVector(d_monomials, n)) {
    d_monomials.push_back(n);
    Trace("nl-ext-debug") << "Register monomial : " << n << std::endl;
    if (n.getKind() == kind::NONLINEAR_MULT) {
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
    if (QuantArith::getMonomialSumLit(atom, msum)) {
      Trace("nl-ext-debug") << "got monomial sum: " << std::endl;
      if (Trace.isOn("nl-ext-debug")) {
        QuantArith::debugPrintMonomialSum(msum, "nl-ext-debug");
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
        int res = QuantArith::isolate(m, msum, coeff, rhs, atom.getKind());
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
  return k == kind::PLUS || k == kind::MULT || k == kind::NONLINEAR_MULT;
}

Node NonlinearExtension::mkLit(Node a, Node b, int status, int orderType) {
  if (status == 0) {
    Node a_eq_b = a.eqNode(b);
    if (orderType == 0) {
      return a_eq_b;
    } else {
      // return mkAbs( a ).eqNode( mkAbs( b ) );
      Node negate_b = NodeManager::currentNM()->mkNode(kind::UMINUS, b);
      return a_eq_b.orNode(a.eqNode(negate_b));
    }
  } else if (status < 0) {
    return mkLit(b, a, -status);
  } else {
    Assert(status == 1 || status == 2);
    NodeManager* nm = NodeManager::currentNM();
    Kind greater_op = status == 1 ? kind::GEQ : kind::GT;
    if (orderType == 0) {
      return nm->mkNode(greater_op, a, b);
    } else {
      // return nm->mkNode( greater_op, mkAbs( a ), mkAbs( b ) );
      Node zero = mkRationalNode(0);
      Node a_is_nonnegative = nm->mkNode(kind::GEQ, a, zero);
      Node b_is_nonnegative = nm->mkNode(kind::GEQ, b, zero);
      Node negate_a = nm->mkNode(kind::UMINUS, a);
      Node negate_b = nm->mkNode(kind::UMINUS, b);
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
    Node a_is_nonnegative = nm->mkNode(kind::GEQ, a, mkRationalNode(0));
    return a_is_nonnegative.iteNode(a, nm->mkNode(kind::UMINUS, a));
  }
}

// by a <k1> b, a <k2> b, we know a <ret> b
Kind NonlinearExtension::joinKinds(Kind k1, Kind k2) {
  if (k2 < k1) {
    return joinKinds(k2, k1);
  } else if (k1 == k2) {
    return k1;
  } else {
    Assert(k1 == kind::EQUAL || k1 == kind::LT || k1 == kind::LEQ ||
           k1 == kind::GT || k1 == kind::GEQ);
    Assert(k2 == kind::EQUAL || k2 == kind::LT || k2 == kind::LEQ ||
           k2 == kind::GT || k2 == kind::GEQ);
    if (k1 == kind::EQUAL) {
      if (k2 == kind::LEQ || k2 == kind::GEQ) {
        return k1;
      }
    } else if (k1 == kind::LT) {
      if (k2 == kind::LEQ) {
        return k1;
      }
    } else if (k1 == kind::LEQ) {
      if (k2 == kind::GEQ) {
        return kind::EQUAL;
      }
    } else if (k1 == kind::GT) {
      if (k2 == kind::GEQ) {
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
    Assert(k1 == kind::EQUAL || k1 == kind::LT || k1 == kind::LEQ ||
           k1 == kind::GT || k1 == kind::GEQ);
    Assert(k2 == kind::EQUAL || k2 == kind::LT || k2 == kind::LEQ ||
           k2 == kind::GT || k2 == kind::GEQ);
    if (k1 == kind::EQUAL) {
      return k2;
    } else if (k1 == kind::LT) {
      if (k2 == kind::LEQ) {
        return k1;
      }
    } else if (k1 == kind::GT) {
      if (k2 == kind::GEQ) {
        return k1;
      }
    }
    return UNDEFINED_KIND;
  }
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
  Node ret = safeConstructNary(kind::MULT, children);
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

std::set<Node> NonlinearExtension::getFalseInModel(
    const std::vector<Node>& assertions) {
  std::set<Node> false_asserts;
  for (size_t i = 0; i < assertions.size(); ++i) {
    Node lit = assertions[i];
    Node litv = computeModelValue(lit);
    Trace("nl-ext-mv") << "M[[ " << lit << " ]] -> " << litv;
    if (litv != d_true) {
      Trace("nl-ext-mv") << " [model-false]" << std::endl;
      Assert(litv == d_false);
      false_asserts.insert(lit);
    } else {
      Trace("nl-ext-mv") << std::endl;
    }
  }
  return false_asserts;
}

std::vector<Node> NonlinearExtension::splitOnZeros(
    const std::vector<Node>& ms_vars) {
  std::vector<Node> lemmas;
  if (!options::nlExtSplitZero()) {
    return lemmas;
  }
  for (unsigned i = 0; i < ms_vars.size(); i++) {
    Node v = ms_vars[i];
    if (d_zero_split.insert(v)) {
      Node lem = v.eqNode(d_zero);
      lem = Rewriter::rewrite(lem);
      d_containing.getValuation().ensureLiteral(lem);
      d_containing.getOutputChannel().requirePhase(lem, true);
      lem = NodeManager::currentNM()->mkNode(kind::OR, lem, lem.negate());
      lemmas.push_back(lem);
    }
  }
  return lemmas;
}

void NonlinearExtension::checkLastCall(const std::vector<Node>& assertions,
                                       const std::set<Node>& false_asserts) {
  // processed monomials
  std::map<Node, bool> ms_proc;

  // list of monomials
  std::vector<Node> ms;
  d_containing.getExtTheory()->getTerms(ms);
  // list of variables occurring in monomials
  std::vector<Node> ms_vars;

  // register monomials
  Trace("nl-ext-mv") << "Monomials : " << std::endl;
  for (unsigned j = 0; j < ms.size(); j++) {
    Node a = ms[j];
    registerMonomial(a);
    computeModelValue(a, 0);
    computeModelValue(a, 1);
    Assert(d_mv[1][a].isConst());
    Assert(d_mv[0][a].isConst());
    Trace("nl-ext-mv") << "  " << a << " -> " << d_mv[1][a] << " ["
                       << d_mv[0][a] << "]" << std::endl;

    std::map<Node, std::vector<Node> >::iterator itvl = d_m_vlist.find(a);
    Assert(itvl != d_m_vlist.end());
    for (unsigned k = 0; k < itvl->second.size(); k++) {
      if (!IsInVector(ms_vars, itvl->second[k])) {
        ms_vars.push_back(itvl->second[k]);
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
  }

  // register constants
  registerMonomial(d_one);
  for (unsigned j = 0; j < d_order_points.size(); j++) {
    Node c = d_order_points[j];
    computeModelValue(c, 0);
    computeModelValue(c, 1);
  }

  int lemmas_proc;
  std::vector<Node> lemmas;

  // register variables
  Trace("nl-ext-mv") << "Variables : " << std::endl;
  Trace("nl-ext") << "Get zero split lemmas..." << std::endl;
  for (unsigned i = 0; i < ms_vars.size(); i++) {
    Node v = ms_vars[i];
    registerMonomial(v);
    computeModelValue(v, 0);
    computeModelValue(v, 1);
    Trace("nl-ext-mv") << "  " << v << " -> " << d_mv[0][v] << std::endl;
  }

  // possibly split on zero?
  lemmas = splitOnZeros(ms_vars);
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas."
                    << std::endl;
    return;
  }

  //-----------------------------------lemmas based on sign (comparison to zero)
  std::map<Node, int> signs;
  Trace("nl-ext") << "Get sign lemmas..." << std::endl;
  for (unsigned j = 0; j < ms.size(); j++) {
    Node a = ms[j];
    if (ms_proc.find(a) == ms_proc.end()) {
      std::vector<Node> exp;
      Trace("nl-ext-debug") << "  process " << a << "..." << std::endl;
      signs[a] = compareSign(a, a, 0, 1, exp, lemmas);
      if (signs[a] == 0) {
        ms_proc[a] = true;
        Trace("nl-ext-mv") << "...mark " << a
                           << " reduced since its value is 0." << std::endl;
      }
    }
  }
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas."
                    << std::endl;
    return;
  }

  //-----------------------------lemmas based on magnitude of non-zero monomials
  for (unsigned r = 1; r <= 1; r++) {
    assignOrderIds(ms_vars, d_order_vars[r], r);

    // sort individual variable lists
    SortNonlinearExtension smv;
    smv.d_nla = this;
    smv.d_order_type = r;
    smv.d_reverse_order = true;
    for (unsigned j = 0; j < ms.size(); j++) {
      std::sort(d_m_vlist[ms[j]].begin(), d_m_vlist[ms[j]].end(), smv);
    }
    for (unsigned c = 0; c < 3; c++) {
      // if (x,y,L) in cmp_infers, then x > y inferred as conclusion of L
      // in lemmas
      std::map<int, std::map<Node, std::map<Node, Node> > > cmp_infers;
      Trace("nl-ext") << "Get comparison lemmas (order=" << r
                      << ", compare=" << c << ")..." << std::endl;
      for (unsigned j = 0; j < ms.size(); j++) {
        Node a = ms[j];
        if (ms_proc.find(a) == ms_proc.end()) {
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
              for (unsigned k = 0; k < ms_vars.size(); k++) {
                Node v = ms_vars[k];
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
            } else {
              // compare magnitude against other non-linear monomials
              for (unsigned k = (j + 1); k < ms.size(); k++) {
                Node b = ms[k];
                //(signs[a]==signs[b])==(r==0)
                if (ms_proc.find(b) == ms_proc.end()) {
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
      lemmas_proc = flushLemmas(nr_lemmas);
      if (lemmas_proc > 0) {
        Trace("nl-ext") << "  ...finished with " << lemmas_proc
                        << " new lemmas (out of possible " << lemmas.size()
                        << ")." << std::endl;
        return;
      }
    }
  }

  // sort monomials by degree
  SortNonlinearExtension snlad;
  snlad.d_nla = this;
  snlad.d_order_type = 4;
  snlad.d_reverse_order = false;
  std::sort(ms.begin(), ms.end(), snlad);
  // all monomials
  std::vector<Node> terms;
  terms.insert(terms.end(), ms_vars.begin(), ms_vars.end());
  terms.insert(terms.end(), ms.begin(), ms.end());

  // term -> coeff -> rhs -> ( status, exp, b ),
  //   where we have that : exp =>  ( coeff * term <status> rhs )
  //   b is true if degree( term ) >= degree( rhs )
  std::map<Node, std::map<Node, std::map<Node, Kind> > > ci;
  std::map<Node, std::map<Node, std::map<Node, Node> > > ci_exp;
  std::map<Node, std::map<Node, std::map<Node, bool> > > ci_max;

  // If ( m, p1, true ), then it would help satisfiability if m were ( >
  // if p1=true, < if p1=false )
  std::map<Node, std::map<bool, bool> > tplane_refine_dir;

  // register constraints
  Trace("nl-ext-debug") << "Register bound constraints..." << std::endl;
  for (context::CDList<Assertion>::const_iterator it =
           d_containing.facts_begin();
       it != d_containing.facts_end(); ++it) {
    Node lit = (*it).assertion;
    bool polarity = lit.getKind() != kind::NOT;
    Node atom = lit.getKind() == kind::NOT ? lit[0] : lit;
    registerConstraint(atom);
    bool is_false_lit = false_asserts.find(lit) != false_asserts.end();
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
          if (type == kind::EQUAL) {
            // we will take the strict inequality in the direction of the
            // model
            Node lhs = QuantArith::mkCoeffTerm(coeff, x);
            Node query = NodeManager::currentNM()->mkNode(kind::GT, lhs, rhs);
            Node query_mv = computeModelValue(query, 1);
            if (query_mv == d_true) {
              exp = query;
              type = kind::GT;
            } else {
              Assert(query_mv == d_false);
              exp = NodeManager::currentNM()->mkNode(kind::LT, lhs, rhs);
              type = kind::LT;
            }
          } else {
            type = negateKind(type);
          }
        }
        // add to status if maximal degree
        ci_max[x][coeff][rhs] = itcm->second.find(x) != itcm->second.end();
        if (Trace.isOn("nl-ext-bound-debug2")) {
          Node t = QuantArith::mkCoeffTerm(coeff, x);
          Trace("nl-ext-bound-debug2")
              << "Add Bound: " << t << " " << type << " " << rhs << " by "
              << exp << std::endl;
        }
        bool updated = true;
        std::map<Node, Kind>::iterator its = ci[x][coeff].find(rhs);
        if (its == ci[x][coeff].end()) {
          ci[x][coeff][rhs] = type;
          ci_exp[x][coeff][rhs] = exp;
        } else if (type != its->second) {
          Trace("nl-ext-bound-debug2")
              << "Joining kinds : " << type << " " << its->second << std::endl;
          Kind jk = joinKinds(type, its->second);
          if (jk == kind::UNDEFINED_KIND) {
            updated = false;
          } else if (jk != its->second) {
            if (jk == type) {
              ci[x][coeff][rhs] = type;
              ci_exp[x][coeff][rhs] = exp;
            } else {
              ci[x][coeff][rhs] = jk;
              ci_exp[x][coeff][rhs] = NodeManager::currentNM()->mkNode(
                  kind::AND, ci_exp[x][coeff][rhs], exp);
            }
          } else {
            updated = false;
          }
        }
        if (Trace.isOn("nl-ext-bound")) {
          if (updated) {
            Trace("nl-ext-bound") << "Bound: ";
            debugPrintBound("nl-ext-bound", coeff, x, ci[x][coeff][rhs], rhs);
            Trace("nl-ext-bound") << " by " << ci_exp[x][coeff][rhs];
            if (ci_max[x][coeff][rhs]) {
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
            bool needsRefine = false;
            bool refineDir;
            if (rhs_v == x_v) {
              if (type == kind::GT) {
                needsRefine = true;
                refineDir = true;
              } else if (type == kind::LT) {
                needsRefine = true;
                refineDir = false;
              }
            } else if (x_v.getConst<Rational>() > rhs_v.getConst<Rational>()) {
              if (type != kind::GT && type != kind::GEQ) {
                needsRefine = true;
                refineDir = false;
              }
            } else {
              if (type != kind::LT && type != kind::LEQ) {
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
              tplane_refine_dir[x][refineDir] = true;
            }
          }
        }
      }
    }
  }
  // reflexive constraints
  Node null_coeff;
  for (unsigned j = 0; j < terms.size(); j++) {
    Node n = terms[j];
    ci[n][null_coeff][n] = kind::EQUAL;
    ci_exp[n][null_coeff][n] = d_true;
    ci_max[n][null_coeff][n] = false;
  }

  //-----------------------------------------------------------------------------------------inferred
  // bounds lemmas, e.g. x >= t => y*x >= y*t
  Trace("nl-ext") << "Get inferred bound lemmas..." << std::endl;

  std::vector<Node> nt_lemmas;
  for (unsigned k = 0; k < terms.size(); k++) {
    Node x = terms[k];
    Trace("nl-ext-bound-debug")
        << "Process bounds for " << x << " : " << std::endl;
    std::map<Node, std::vector<Node> >::iterator itm =
        d_m_contain_parent.find(x);
    if (itm != d_m_contain_parent.end()) {
      Trace("nl-ext-bound-debug") << "...has " << itm->second.size()
                                  << " parent monomials." << std::endl;
      // check derived bounds
      std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itc =
          ci.find(x);
      if (itc != ci.end()) {
        for (std::map<Node, std::map<Node, Kind> >::iterator itcc =
                 itc->second.begin();
             itcc != itc->second.end(); ++itcc) {
          Node coeff = itcc->first;
          Node t = QuantArith::mkCoeffTerm(coeff, x);
          for (std::map<Node, Kind>::iterator itcr = itcc->second.begin();
               itcr != itcc->second.end(); ++itcr) {
            Node rhs = itcr->first;
            // only consider this bound if maximal degree
            if (ci_max[x][coeff][rhs]) {
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
                Assert(mmv.isConst());
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
                      NodeManager::currentNM()->mkNode(kind::MULT, mult, t);
                  Node infer_rhs =
                      NodeManager::currentNM()->mkNode(kind::MULT, mult, rhs);
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
                        kind::AND,
                        NodeManager::currentNM()->mkNode(
                            mmv_sign == 1 ? kind::GT : kind::LT, mult, d_zero),
                        ci_exp[x][coeff][rhs]);
                    Node iblem = NodeManager::currentNM()->mkNode(kind::IMPLIES,
                                                                  exp, infer);
                    Node pr_iblem = iblem;
                    iblem = Rewriter::rewrite(iblem);
                    bool introNewTerms = hasNewMonomials(iblem, ms);
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
              }
            }
          }
        }
      }
    } else {
      Trace("nl-ext-bound-debug") << "...has no parent monomials." << std::endl;
    }
  }
  // Trace("nl-ext") << "Bound lemmas : " << lemmas.size() << ", " <<
  // nt_lemmas.size() << std::endl;  prioritize lemmas that do not
  // introduce new monomials
  lemmas_proc = flushLemmas(lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas."
                    << std::endl;
    return;
  }

  //------------------------------------resolution bound inferences, e.g.
  //(
  // y>=0 ^ s <= x*z ^ x*y <= t ) => y*s <= z*t
  if (options::nlExtResBound()) {
    Trace("nl-ext") << "Get resolution inferred bound lemmas..." << std::endl;
    for (unsigned j = 0; j < terms.size(); j++) {
      Node a = terms[j];
      std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itca =
          ci.find(a);
      if (itca != ci.end()) {
        for (unsigned k = (j + 1); k < terms.size(); k++) {
          Node b = terms[k];
          std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator
              itcb = ci.find(b);
          if (itcb != ci.end()) {
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
                  Node rhs_a_res_base = NodeManager::currentNM()->mkNode(
                      kind::MULT, itb->second, rhs_a);
                  rhs_a_res_base = Rewriter::rewrite(rhs_a_res_base);
                  if (!hasNewMonomials(rhs_a_res_base, ms)) {
                    Kind type_a = itcar->second;
                    exp.push_back(ci_exp[a][coeff_a][rhs_a]);

                    // bounds of b
                    for (std::map<Node, std::map<Node, Kind> >::iterator itcbc =
                             itcb->second.begin();
                         itcbc != itcb->second.end(); ++itcbc) {
                      Node coeff_b = itcbc->first;
                      Node rhs_a_res =
                          QuantArith::mkCoeffTerm(coeff_b, rhs_a_res_base);
                      for (std::map<Node, Kind>::iterator itcbr =
                               itcbc->second.begin();
                           itcbr != itcbc->second.end(); ++itcbr) {
                        Node rhs_b = itcbr->first;
                        Node rhs_b_res = NodeManager::currentNM()->mkNode(
                            kind::MULT, ita->second, rhs_b);
                        rhs_b_res = QuantArith::mkCoeffTerm(coeff_a, rhs_b_res);
                        rhs_b_res = Rewriter::rewrite(rhs_b_res);
                        if (!hasNewMonomials(rhs_b_res, ms)) {
                          Kind type_b = itcbr->second;
                          exp.push_back(ci_exp[b][coeff_b][rhs_b]);
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
                                  kind::GT, pivot_factor, d_zero));
                            } else {
                              exp.push_back(NodeManager::currentNM()->mkNode(
                                  kind::LT, pivot_factor, d_zero));
                            }
                          }
                          Kind jk = transKinds(types[0], types[1]);
                          Trace("nl-ext-rbound-debug")
                              << "trans kind : " << types[0] << " + "
                              << types[1] << " = " << jk << std::endl;
                          if (jk != kind::UNDEFINED_KIND) {
                            Node conc = NodeManager::currentNM()->mkNode(
                                jk, rhs_a_res, rhs_b_res);
                            Node conc_mv = computeModelValue(conc, 1);
                            if (conc_mv == d_false) {
                              Node rblem = NodeManager::currentNM()->mkNode(
                                  kind::IMPLIES,
                                  NodeManager::currentNM()->mkNode(kind::AND,
                                                                   exp),
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
    lemmas_proc = flushLemmas(lemmas);
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas."
                      << std::endl;
      return;
    }
  }

  // from inferred bound inferences
  lemmas_proc = flushLemmas(nt_lemmas);
  if (lemmas_proc > 0) {
    Trace("nl-ext") << "  ...finished with " << lemmas_proc
                    << " new (monomial-introducing) lemmas." << std::endl;
    return;
  }

  if (options::nlExtTangentPlanes()) {
    Trace("nl-ext") << "Get tangent plane lemmas..." << std::endl;
    unsigned kstart = ms_vars.size();
    for (unsigned k = kstart; k < terms.size(); k++) {
      Node t = terms[k];
      // if this term requires a refinement
      if (tplane_refine_dir.find(t) != tplane_refine_dir.end()) {
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
                Node a_v = computeModelValue(a, 1);
                Node b_v = computeModelValue(b, 1);
                // tangent plane
                Node tplane = NodeManager::currentNM()->mkNode(
                    kind::MINUS,
                    NodeManager::currentNM()->mkNode(
                        kind::PLUS,
                        NodeManager::currentNM()->mkNode(kind::MULT, b_v, a),
                        NodeManager::currentNM()->mkNode(kind::MULT, a_v, b)),
                    NodeManager::currentNM()->mkNode(kind::MULT, a_v, b_v));
                for (unsigned d = 0; d < 4; d++) {
                  Node aa = NodeManager::currentNM()->mkNode(
                      d == 0 || d == 3 ? kind::GEQ : kind::LEQ, a, a_v);
                  Node ab = NodeManager::currentNM()->mkNode(
                      d == 1 || d == 3 ? kind::GEQ : kind::LEQ, b, b_v);
                  Node conc = NodeManager::currentNM()->mkNode(
                      d <= 1 ? kind::LEQ : kind::GEQ, t, tplane);
                  Node tlem = NodeManager::currentNM()->mkNode(
                      kind::OR, aa.negate(), ab.negate(), conc);
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
    Trace("nl-ext") << "...trying " << lemmas.size()
                    << " tangent plane lemmas..." << std::endl;
    lemmas_proc = flushLemmas(lemmas);
    if (lemmas_proc > 0) {
      Trace("nl-ext") << "  ...finished with " << lemmas_proc << " new lemmas."
                      << std::endl;
      return;
    }
  }

  Trace("nl-ext") << "...set incomplete" << std::endl;
  d_containing.getOutputChannel().setIncomplete();
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
    Assert(e == Theory::EFFORT_LAST_CALL);
    Trace("nl-ext-mv") << "Getting model values... check for [model-false]"
                       << std::endl;
    d_mv[0].clear();
    d_mv[1].clear();
    std::vector<Node> assertions;
    for (Theory::assertions_iterator it = d_containing.facts_begin();
         it != d_containing.facts_end(); ++it) {
      const Assertion& assertion = *it;
      assertions.push_back(assertion.assertion);
    }
    
    const std::set<Node> false_asserts = getFalseInModel(assertions);
    if (!false_asserts.empty()) {
      checkLastCall(assertions, false_asserts);
    }else{
      //must ensure that shared terms are equal to their concrete value
      std::vector< Node > lemmas;
      for (context::CDList<TNode>::const_iterator its = d_containing.shared_terms_begin();
           its != d_containing.shared_terms_end(); ++its) {
        TNode shared_term = *its;
        Node stv0 = computeModelValue( shared_term, 0 );
        Node stv1 = computeModelValue( shared_term, 1 );
        
        if( stv0!=stv1 ){
          Trace("nl-ext-mv") << "Bad shared term value : " << shared_term << " : " << stv1 << ", actual is " << stv0 << std::endl;
          //split on the value, FIXME : this is non-terminating in general, improve this
          Node lem = shared_term.eqNode(stv0);
          lem = Rewriter::rewrite(lem);
          d_containing.getValuation().ensureLiteral(lem);
          d_containing.getOutputChannel().requirePhase(lem, true);
          lem = NodeManager::currentNM()->mkNode(kind::OR, lem, lem.negate());
          lemmas.push_back(lem);
        }
      }
      if( !lemmas.empty() ){
        int lemmas_proc = flushLemmas(lemmas);
        Trace("nl-ext-mv") << "...added " << lemmas_proc << " shared term split lemmas." << std::endl;
        Assert( lemmas_proc>0 );
      }
    }
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
    return compare_value(get_compare_value(i, orderType),
                         get_compare_value(j, orderType), orderType);
    // minimal degree
  } else if (orderType == 4) {
    unsigned i_count = getCount(d_m_degree, i);
    unsigned j_count = getCount(d_m_degree, j);
    return i_count == j_count ? 0 : (i_count < j_count ? 1 : -1);
  } else {
    return 0;
  }
}

int NonlinearExtension::compare_value(Node i, Node j,
                                      unsigned orderType) const {
  Assert(orderType >= 0 && orderType <= 3);
  Trace("nl-ext-debug") << "compare_value " << i << " " << j
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
  Trace("nl-ext-debug") << "Compare variable " << i << " " << orderType
                        << std::endl;
  Assert(orderType >= 0 && orderType <= 3);
  unsigned mindex = orderType <= 1 ? 0 : 1;
  std::map<Node, Node>::const_iterator iti = d_mv[mindex].find(i);
  Assert(iti != d_mv[mindex].end());
  return iti->second;
}

// trying to show a <> 0 by inequalities between variables in monomial a w.r.t
// 0
int NonlinearExtension::compareSign(Node oa, Node a, unsigned a_index,
                                    int status, std::vector<Node>& exp,
                                    std::vector<Node>& lem) {
  Trace("nl-ext-debug") << "Process " << a << " at index " << a_index
                        << ", status is " << status << std::endl;
  Assert(d_mv[1].find(oa) != d_mv[1].end());
  if (a_index == d_m_vlist[a].size()) {
    if (d_mv[1][oa].getConst<Rational>().sgn() != status) {
      Node lemma = safeConstructNary(kind::AND, exp)
                       .impNode(mkLit(oa, d_zero, status * 2));
      lem.push_back(lemma);
    }
    return status;
  } else {
    Assert(a_index < d_m_vlist[a].size());
    Node av = d_m_vlist[a][a_index];
    unsigned aexp = d_m_exp[a][av];
    // take current sign in model
    Assert(d_mv[0].find(av) != d_mv[0].end());
    int sgn = d_mv[0][av].getConst<Rational>().sgn();
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
        exp.push_back(NodeManager::currentNM()->mkNode(
            sgn == 1 ? kind::GT : kind::LT, av, d_zero));
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
          kind::IMPLIES, safeConstructNary(kind::AND, exp),
          mkLit(oa, ob, status, 1));
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
      Assert(d_order_vars[1].find(av) != d_order_vars[1].end());
      avo = d_order_vars[1][av];
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
      Assert(d_order_vars[1].find(bv) != d_order_vars[1].end());
      bvo = d_order_vars[1][bv];
    }
    // get "one" information
    Assert(d_order_vars[1].find(d_one) != d_order_vars[1].end());
    unsigned ovo = d_order_vars[1][d_one];
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

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
