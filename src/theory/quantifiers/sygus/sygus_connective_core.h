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
  bool isFalse(const std::vector<Node>& is) const;
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
  /** common constants */
  Node d_true;
  Node d_false;
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
    /**
     * Points that satisfy d_this.
     */
    NodeTrie d_refinementPt;
    unsigned d_numFalseCores;
    std::unordered_set<Node, NodeHashFunction> d_tried;
    bool isActive() const { return !d_scons.isNull(); }
    Node getSygusSolution(std::vector<Node>& conjs) const;

    /**
     * Get a refinement point that n evalutes to true on, taken from the
     * d_refinementPt trie, and store it in ss. The set visited is the set
     * of leaf nodes that we've already checked.
     */
    Node getRefinementPt(SygusConnectiveCore* p,
                         Node n,
                         std::unordered_set<Node, NodeHashFunction>& visited,
                         std::vector<Node>& ss);
    /**
     * Selects a node from passerts that evaluates to false on point mv if one
     * exists, or otherwise returns null.
     *
     * If a non-null node is returned, it is removed from passerts.
     */
    bool addToAsserts(SygusConnectiveCore* p,
                      std::vector<Node>& passerts,
                      const std::vector<Node>& mvs,
                      Node mvId,
                      std::vector<Node>& asserts,
                      Node& an);
  };
  /** Above information for the precondition of the synthesis conjecture */
  Component d_pre;
  /** Above information for the postcondition of the synthesis conjecture */
  Component d_post;
  /** the free variables that may appear in solutions */
  std::vector<Node> d_vars;
  /** The evaluation term */
  Node d_eterm;

  void getModel(SmtEngine& smt, std::vector<Node>& mvs);

  std::unordered_map<Node,
                     std::unordered_map<Node, Node, NodeHashFunction>,
                     NodeHashFunction>
      d_eval_cache;
  Node evaluate(Node n, Node id, const std::vector<Node>& mvs);

  Result checkSat(Node n, std::vector<Node>& mvs);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
