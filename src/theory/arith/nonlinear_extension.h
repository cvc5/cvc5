/*********************                                                        */
/*! \file nonlinear_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extensions for incomplete handling of nonlinear multiplication.
 **
 ** Extensions to the theory of arithmetic incomplete handling of nonlinear
 ** multiplication via axiom instantiations.
 **/

#ifndef __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H
#define __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H

#include <stdint.h>

#include <map>
#include <queue>
#include <set>
#include <utility>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/theory_arith.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::map<Node, unsigned> NodeMultiset;

class NonlinearExtension {
 public:
  NonlinearExtension(TheoryArith& containing, eq::EqualityEngine* ee);
  ~NonlinearExtension();
  bool getCurrentSubstitution(int effort, const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp);

  std::pair<bool, Node> isExtfReduced(int effort, Node n, Node on,
                                      const std::vector<Node>& exp) const;
  void check(Theory::Effort e);
  bool needsCheckLastEffort() const { return d_needsLastCall; }
  int compare(Node i, Node j, unsigned orderType) const;
  int compare_value(Node i, Node j, unsigned orderType) const;

  bool isMonomialSubset(Node a, Node b) const;
  void registerMonomialSubset(Node a, Node b);

 private:
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

  // monomial information (context-independent)
  class MonomialIndex {
   public:
    // status 0 : n equal, -1 : n superset, 1 : n subset
    void addTerm(Node n, const std::vector<Node>& reps, NonlinearExtension* nla,
                 int status = 0, unsigned argIndex = 0);

   private:
    std::map<Node, MonomialIndex> d_data;
    std::vector<Node> d_monos;
  }; /* class MonomialIndex */

  // constraint information (context-independent)
  struct ConstraintInfo {
   public:
    Node d_rhs;
    Node d_coeff;
    Kind d_type;
  }; /* struct ConstraintInfo */

  // Check assertions for consistency in the effort LAST_CALL with a subset of
  // the assertions, false_asserts, evaluate to false in the current model.
  void checkLastCall(const std::vector<Node>& assertions,
                     const std::set<Node>& false_asserts);

  // Returns a vector containing a split on whether each term is 0 or not for
  // those terms that have not been split on in the current context.
  std::vector<Node> splitOnZeros(const std::vector<Node>& terms);

  static bool isArithKind(Kind k);
  static Node mkLit(Node a, Node b, int status, int orderType = 0);
  static Node mkAbs(Node a);
  static Kind joinKinds(Kind k1, Kind k2);
  static Kind transKinds(Kind k1, Kind k2);
  Node mkMonomialRemFactor(Node n, const NodeMultiset& n_exp_rem) const;

  // register monomial
  void registerMonomial(Node n);
  void setMonomialFactor(Node a, Node b, const NodeMultiset& common);

  void registerConstraint(Node atom);
  // index = 0 : concrete, 1 : abstract
  Node computeModelValue(Node n, unsigned index = 0);

  Node get_compare_value(Node i, unsigned orderType) const;
  void assignOrderIds(std::vector<Node>& vars, NodeMultiset& d_order,
                      unsigned orderType);

  // Returns the subset of assertions that evaluate to false in the model.
  std::set<Node> getFalseInModel(const std::vector<Node>& assertions);

  // status
  // 0 : equal
  // 1 : greater than or equal
  // 2 : greater than
  // -X : (less)
  // in these functions we are iterating over variables of monomials
  // initially : exp => ( oa = a ^ ob = b )
  int compareSign(Node oa, Node a, unsigned a_index, int status,
                  std::vector<Node>& exp, std::vector<Node>& lem);
  bool compareMonomial(
      Node oa, Node a, NodeMultiset& a_exp_proc, Node ob, Node b,
      NodeMultiset& b_exp_proc, std::vector<Node>& exp, std::vector<Node>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  bool compareMonomial(
      Node oa, Node a, unsigned a_index, NodeMultiset& a_exp_proc, Node ob,
      Node b, unsigned b_index, NodeMultiset& b_exp_proc, int status,
      std::vector<Node>& exp, std::vector<Node>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  bool cmp_holds(Node x, Node y,
                 std::map<Node, std::map<Node, Node> >& cmp_infers,
                 std::vector<Node>& exp, std::map<Node, bool>& visited);

  bool isEntailed(Node n, bool pol);

  // Potentially sends lem on the output channel if lem has not been sent on the
  // output channel in this context. Returns the number of lemmas sent on the
  // output channel.
  int flushLemma(Node lem);

  // Potentially sends lemmas to the output channel and clears lemmas. Returns
  // the number of lemmas sent to the output channel.
  int flushLemmas(std::vector<Node>& lemmas);

  // Returns the NodeMultiset for an existing monomial.
  const NodeMultiset& getMonomialExponentMap(Node monomial) const;

  // Map from monomials to var^index.
  typedef std::map<Node, NodeMultiset> MonomialExponentMap;
  MonomialExponentMap d_m_exp;

  std::map<Node, std::vector<Node> > d_m_vlist;
  NodeMultiset d_m_degree;
  // monomial index, by sorted variables
  MonomialIndex d_m_index;
  // list of all monomials
  std::vector<Node> d_monomials;
  // containment ordering
  std::map<Node, std::vector<Node> > d_m_contain_children;
  std::map<Node, std::vector<Node> > d_m_contain_parent;
  std::map<Node, std::map<Node, Node> > d_m_contain_mult;
  std::map<Node, std::map<Node, Node> > d_m_contain_umult;
  // ( x*y, x*z, y ) for each pair of monomials ( x*y, x*z ) with common factors
  std::map<Node, std::map<Node, Node> > d_mono_diff;

  // cache of all lemmas sent
  NodeSet d_lemmas;
  NodeSet d_zero_split;

  // utilities
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  Node d_false;

  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;

  // pointer to used equality engine
  eq::EqualityEngine* d_ee;
  // needs last call effort
  bool d_needsLastCall;

  // if d_c_info[lit][x] = ( r, coeff, k ), then ( lit <=>  (coeff * x) <k> r )
  std::map<Node, std::map<Node, ConstraintInfo> > d_c_info;
  std::map<Node, std::map<Node, bool> > d_c_info_maxm;
  std::vector<Node> d_constraints;

  // model values/orderings
  // model values
  std::map<Node, Node> d_mv[2];

  // ordering, stores variables and 0,1,-1
  std::map<unsigned, NodeMultiset> d_order_vars;
  std::vector<Node> d_order_points;
}; /* class NonlinearExtension */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
