/*********************                                                        */
/*! \file nl_monomial.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for monomials
 **/

#ifndef CVC4__THEORY__ARITH__NL__NL_MONOMIAL_H
#define CVC4__THEORY__ARITH__NL__NL_MONOMIAL_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class MonomialDb;
class NlModel;

typedef std::map<Node, unsigned> NodeMultiset;
typedef std::map<Node, NodeMultiset> MonomialExponentMap;

/** An index data structure for node multisets (monomials) */
class MonomialIndex
{
 public:
  /**
   * Add term to this trie. The argument status indicates what the status
   * of n is with respect to the current node in the trie, where:
   *   0 : n is equal, -1 : n is superset, 1 : n is subset
   * of the node described by the current path in the trie.
   */
  void addTerm(Node n,
               const std::vector<Node>& reps,
               MonomialDb* nla,
               int status = 0,
               unsigned argIndex = 0);

 private:
  /** The children of this node */
  std::map<Node, MonomialIndex> d_data;
  /** The monomials at this node */
  std::vector<Node> d_monos;
}; /* class MonomialIndex */

/** Context-independent database for monomial information */
class MonomialDb
{
 public:
  MonomialDb();
  ~MonomialDb() {}
  /** register monomial */
  void registerMonomial(Node n);
  /**
   * Register monomial subset. This method is called when we infer that b is
   * a subset of monomial a, e.g. x*y^2 is a subset of x^3*y^2*z.
   */
  void registerMonomialSubset(Node a, Node b);
  /**
   * returns true if the multiset containing the
   * factors of monomial a is a subset of the multiset
   * containing the factors of monomial b.
   */
  bool isMonomialSubset(Node a, Node b) const;
  /** Returns the NodeMultiset for a registered monomial. */
  const NodeMultiset& getMonomialExponentMap(Node monomial) const;
  /** Returns the exponent of variable v in the given monomial */
  unsigned getExponent(Node monomial, Node v) const;
  /** Get the list of unique variables is the monomial */
  const std::vector<Node>& getVariableList(Node monomial) const;
  /** Get degree of monomial, e.g. the degree of x^2*y^2 = 4 */
  unsigned getDegree(Node monomial) const;
  /** Sort monomials in ms by their degree
   *
   * Updates ms so that degree(ms[i]) <= degree(ms[j]) for i <= j.
   */
  void sortByDegree(std::vector<Node>& ms) const;
  /** Sort the variable lists based on model values
   *
   * This updates the variable lists of monomials in ms based on the absolute
   * value of their current model values in m.
   *
   * In other words, for each i, getVariableList(ms[i]) returns
   * v1, ..., vn where |m(v1)| <= ... <= |m(vn)| after this method is invoked.
   */
  void sortVariablesByModel(std::vector<Node>& ms, NlModel& m);
  /** Get monomial contains children map
   *
   * This maps monomials to other monomials that are contained in them, e.g.
   * x^2 * y may map to { x, x^2, y } if these three terms exist have been
   * registered to this class.
   */
  const std::map<Node, std::vector<Node> >& getContainsChildrenMap();
  /** Get monomial contains parent map, reverse of above */
  const std::map<Node, std::vector<Node> >& getContainsParentMap();
  /**
   * Get contains difference. Return the difference of a and b or null if it
   * does not exist. In other words, this returns a term equivalent to a/b
   * that does not contain division.
   */
  Node getContainsDiff(Node a, Node b) const;
  /**
   * Get contains difference non-linear. Same as above, but stores terms of kind
   * NONLINEAR_MULT instead of MULT.
   */
  Node getContainsDiffNl(Node a, Node b) const;
  /** Make monomial remainder factor */
  Node mkMonomialRemFactor(Node n, const NodeMultiset& n_exp_rem) const;

 private:
  /** commonly used terms */
  Node d_one;
  /** list of all monomials */
  std::vector<Node> d_monomials;
  /** Map from monomials to var^index. */
  MonomialExponentMap d_m_exp;
  /**
   * Mapping from monomials to the list of variables that occur in it. For
   * example, x*x*y*z -> { x, y, z }.
   */
  std::map<Node, std::vector<Node> > d_m_vlist;
  /** Degree information */
  std::map<Node, unsigned> d_m_degree;
  /** monomial index, by sorted variables */
  MonomialIndex d_m_index;
  /** containment ordering */
  std::map<Node, std::vector<Node> > d_m_contain_children;
  std::map<Node, std::vector<Node> > d_m_contain_parent;
  std::map<Node, std::map<Node, Node> > d_m_contain_mult;
  std::map<Node, std::map<Node, Node> > d_m_contain_umult;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_MONOMIAL_H */
