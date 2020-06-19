/*********************                                                        */
/*! \file nl_lemma_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for processing lemmas from the non-linear solver
 **/

#ifndef CVC4__THEORY__ARITH__NL__NL_LEMMA_UTILS_H
#define CVC4__THEORY__ARITH__NL__NL_LEMMA_UTILS_H

#include <tuple>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class NlModel;

/**
 * The data structure for a single lemma to process by the non-linear solver,
 * including the lemma itself and whether it should be preprocessed (see
 * OutputChannel::lemma).
 *
 * This also includes data structures that encapsulate the side effect of adding
 * this lemma in the non-linear solver. This is used to specify how the state of
 * the non-linear solver should update. This includes:
 * - A set of secant points to record (for transcendental secant plane
 * inferences).
 */
struct NlLemma
{
  NlLemma(Node lem) : d_lemma(lem), d_preprocess(false) {}
  ~NlLemma() {}
  /** The lemma */
  Node d_lemma;
  /** Whether to preprocess the lemma */
  bool d_preprocess;
  /** secant points to add
   *
   * A member (tf, d, c) in this vector indicates that point c should be added
   * to the list of secant points for an application of a transcendental
   * function tf for Taylor degree d. This is used for incremental linearization
   * for underapproximation (resp. overapproximations) of convex (resp.
   * concave) regions of transcendental functions. For details, see
   * Cimatti et al., CADE 2017.
   */
  std::vector<std::tuple<Node, unsigned, Node> > d_secantPoint;
};
/**
 * Writes a non-linear lemma to a stream.
 */
std::ostream& operator<<(std::ostream& out, NlLemma& n);

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
  bool operator()(Node i, Node j);
};

struct SortNonlinearDegree
{
  SortNonlinearDegree(const std::map<Node, unsigned>& m) : d_mdegree(m) {}
  /** pointer to the non-linear extension */
  const std::map<Node, unsigned>& d_mdegree;
  /** Get the degree of n in d_mdegree */
  unsigned getDegree(Node n) const;
  /**
   * Sorts by degree of the monomials, where lower degree monomials come
   * first.
   */
  bool operator()(Node i, Node j);
};

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
  Node add(Node d, const std::vector<Node>& args);
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_LEMMA_UTILS_H */
