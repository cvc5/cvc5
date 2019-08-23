/*********************                                                        */
/*! \file sygus_connective_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus connective core utility.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_CONNECTIVE_CORE_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_CONNECTIVE_CORE_H

#include <unordered_set>
#include "expr/node.h"
#include "expr/node_trie.h"

#include "theory/quantifiers/sygus/cegis.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class FalseCoreTrie
{
 public:
  std::map<Node, FalseCoreTrie> d_children;
  Node d_data;
  bool add(Node n, std::vector<Node>& i);
  Node getExclusion(std::unordered_set<Node, NodeHashFunction>& excAsserts,
                    std::vector<Node>& ctx) const;
};

/** SygusConnectiveCore
 *
 */
class SygusConnectiveCore : public Cegis
{
 public:
  SygusConnectiveCore(QuantifiersEngine* qe, SynthConjecture* p);
  ~SygusConnectiveCore() {}
  /**
   * Return whether this module has the possibility to construct solutions. This
   * is true if this module has been initialized, and the shape of the
   * conjecture allows us to use the connective core algorithm.
   */
  bool isActive() const;

 protected:
  /** do cegis-implementation-specific initialization for this class */
  bool processInitialize(Node conj,
                         Node n,
                         const std::vector<Node>& candidates,
                         std::vector<Node>& lemmas) override;
  /** do cegis-implementation-specific post-processing for construct candidate
   *
   * satisfiedRl is whether all refinement lemmas are satisfied under the
   * substitution { enums -> enum_values }.
   */
  bool processConstructCandidates(const std::vector<Node>& enums,
                                  const std::vector<Node>& enum_values,
                                  const std::vector<Node>& candidates,
                                  std::vector<Node>& candidate_values,
                                  bool satisfiedRl,
                                  std::vector<Node>& lems) override;

  /** construct solution
   *
   * This function is called when candidates -> candidate_values is the current
   * candidate solution for the synthesis conjecture.
   *
   * If this function returns true, then this class adds to solv the
   * a candidate solution for candidates.
   */
  bool constructSolution(const std::vector<Node>& candidates,
                         const std::vector<Node>& candidate_values,
                         std::vector<Node>& solv);

 private:
  /** The candidate */
  TNode d_candidate;
  /**
   * Information about the pre and post conditions of the synthesis conjecture.
   */
  class Component
  {
   public:
    Component() : d_numFalseCores(0) {}
    Node d_this;
    Node d_scons;
    std::vector<Node> d_cpool;
    std::map<Node, Node> d_cpoolToSol;
    FalseCoreTrie d_falseCores;
    unsigned d_numFalseCores;
    std::unordered_set<Node, NodeHashFunction> d_tried;
    bool isActive() const { return !d_scons.isNull(); }
    Node getSygusSolution(std::vector<Node>& conjs) const;
  };
  /** Above information for the precondition of the synthesis conjecture */
  Component d_pre;
  /** Above information for the postcondition of the synthesis conjecture */
  Component d_post;
  /** the free variables that may appear in solutions */
  std::vector<Node> d_vars;
  /** The evaluation term */
  Node d_eterm;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
