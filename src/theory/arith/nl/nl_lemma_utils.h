/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for processing lemmas from the non-linear solver.
 */

#ifndef CVC5__THEORY__ARITH__NL__NL_LEMMA_UTILS_H
#define CVC5__THEORY__ARITH__NL__NL_LEMMA_UTILS_H

#include <tuple>
#include <vector>

#include "expr/node.h"
#include "theory/theory_inference.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class NlModel;
class NonlinearExtension;

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
class NlLemma : public SimpleTheoryLemma
{
 public:
  NlLemma(InferenceId inf,
          Node n,
          LemmaProperty p = LemmaProperty::NONE,
          ProofGenerator* pg = nullptr)
      : SimpleTheoryLemma(inf, n, p, pg)
  {
  }
  ~NlLemma() {}

  TrustNode processLemma(LemmaProperty& p) override;

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

  NonlinearExtension* d_nlext;
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

/**
 * Wrapper for std::sort that uses SortNlModel to sort an iterator range.
 */
template <typename It>
void sortByNlModel(It begin,
                   It end,
                   NlModel* model,
                   bool concrete = true,
                   bool absolute = false,
                   bool reverse = false)
{
  SortNlModel smv;
  smv.d_nlm = model;
  smv.d_isConcrete = concrete;
  smv.d_isAbsolute = absolute;
  smv.d_reverse_order = reverse;
  std::sort(begin, end, smv);
}

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
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL_LEMMA_UTILS_H */
