/*********************                                                        */
/*! \file cegis_core_connective.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Cegis core connective module.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEGIS_CORE_CONNECTIVE_H
#define CVC4__THEORY__QUANTIFIERS__CEGIS_CORE_CONNECTIVE_H

#include <unordered_set>
#include "expr/node.h"
#include "expr/node_trie.h"

#include "theory/evaluator.h"
#include "theory/quantifiers/sygus/cegis.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * A trie for that stores data at undetermined depth. Storing data at
 * undetermined depth is in contrast to the NodeTrie (expr/node_trie.h), which
 * assumes all data is stored at a fixed depth.
 *
 * Since data can be stored at any depth, we require both a d_children field
 * and a d_data field.
 */
class VariadicTrie
{
 public:
  /** the children of this node */
  std::map<Node, VariadicTrie> d_children;
  /** the data at this node */
  Node d_data;
  /**
   * Add data with identifier n indexed by i, return true if data is not already
   * stored at the node indexed by i.
   */
  bool add(Node n, const std::vector<Node>& i);
  /** Is there any data in this trie that is indexed by any subset of is? */
  bool hasSubset(const std::vector<Node>& is) const;
};

/** CegisCoreConnective
 *
 * A sygus module that is specialized in handling conjectures of the form:
 * exists P. forall x. A[x] => C(x) ^ C(x) => B(x)
 * That is, conjectures with a pre/post condition but no inductive relation
 * or other constraints. Additionally, we may have that the above conjecture
 * has a side condition, which requires that exists x. SC[x]^C(x) is
 * satisfiable.
 *
 * Two examples of this kind of sygus conjecture are abduction and
 * interpolation.
 *
 * This module implements a specific algorithm for constructing solutions
 * to this conjecture based on Boolean connectives and unsat cores, described
 * in following.
 *
 *
 */
class CegisCoreConnective : public Cegis
{
 public:
  CegisCoreConnective(QuantifiersEngine* qe, SynthConjecture* p);
  ~CegisCoreConnective() {}
  /**
   * Return whether this module has the possibility to construct solutions. This
   * is true if this module has been initialized, and the shape of the
   * conjecture allows us to use the core connective algorithm.
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
  /** The first-order datatype variable for the function-to-synthesize */
  TNode d_candidate;
  /**
   * Information about the pre and post conditions of the synthesis conjecture.
   * This maintains all information needed for producing solutions relative to
   * one direction of the synthesis conjecture. In other words, this component
   * may be focused on finding a C1 ... Cn such that A => C1 V ... V Cn
   * or alteratively C1 ^ ... ^ Cn such that C1 ^ ... ^ Cn => B.
   */
  class Component
  {
   public:
    Component() : d_numRefPoints(0), d_numFalseCores(0) {}
    /** The original formula for the pre/post condition A/B. */
    Node d_this;
    /**
     * The sygus constructor for constructing solutions based on the core
     * connective algorithm. This is a sygus datatype constructor that
     * encodes applications of AND or OR.
     */
    Node d_scons;
    std::vector<Node> d_cpool;
    /**
     * A map from the formulas in the above vector to their sygus analog.
     */
    std::map<Node, Node> d_cpoolToSol;
    /**
     * An index of list of predicates such that each list ( P1, ..., Pn )
     * indexed by this trie is such that
     */
    VariadicTrie d_falseCores;
    /**
     * The number of points that have been added to the above trie, for
     * debugging.
     */
    unsigned d_numFalseCores;
    /**
     * An index of the points that satisfy d_this.
     */
    NodeTrie d_refinementPt;
    /**
     * The number of points that have been added to the above trie, for
     * debugging.
     */
    unsigned d_numRefPoints;
    std::unordered_set<Node, NodeHashFunction> d_tried;
    /** Is this component active? */
    bool isActive() const { return !d_scons.isNull(); }
    /**
     * Get the sygus solution corresponding to the Boolean connective for
     * this component applied to conj. In particular, this returns a
     * right-associative chain of applications of sygus constructor d_scons
     * to the sygus analog of formulas in conj.
     */
    Node getSygusSolution(std::vector<Node>& conjs) const;
    /** Add a refinement point to this component */
    void addRefinementPt(Node id, const std::vector<Node>& pt);
    /** Add a false case to this component */
    void addFalseCore(Node id, const std::vector<Node>& u);

    /**
     * Get a refinement point that n evalutes to true on, taken from the
     * d_refinementPt trie, and store it in ss. The set visited is the set
     * of leaf nodes (reference by their data) that we have already processed
     * and should be ignored.
     */
    Node getRefinementPt(CegisCoreConnective* p,
                         Node n,
                         std::unordered_set<Node, NodeHashFunction>& visited,
                         std::vector<Node>& ss);
    /**
     * Selects a node from passerts that evaluates to false on point mv if one
     * exists, or otherwise returns null.
     *
     * If a non-null node is returned, it is removed from passerts.
     */
    bool addToAsserts(CegisCoreConnective* p,
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
  /**
   * The free variables that may appear in the pre/post condition, and our
   * pools of predicates.
   */
  std::vector<Node> d_vars;
  /**
   * The evaluation term of the form:
   *   (DT_SYGUS_EVAL d_candidate d_vars[0]...d_vars[n])
   * This is used to convert enumerated sygus terms t to their builtin
   * equivalent via rewriting d_eterm * { d_candidate -> t }.
   */
  Node d_eterm;
  /**
   * The side condition of the conjecture. If this is non-null, then
   * this node is a formula such that (builtin) solutions t' are such that
   * t' ^ d_sc is satisfiable. Notice that the free variables of d_sc are
   * a subset of d_vars.
   */
  Node d_sc;
  //-----------------------------------for SMT engine calls
  /**
   * Assuming smt has just been called to check-sat and returned "SAT", this
   * method adds the model for d_vars to mvs.
   */
  void getModel(SmtEngine& smt, std::vector<Node>& mvs) const;
  /**
   * Assuming smt has just been called to check-sat and returned "SAT", this
   * method get the unsat core and adds it to uasserts.
   *
   * If query is non-null, then it is excluded from uasserts. If query was
   * in the unsat core, then this method returns true. Otherwise, this method
   * returns false. It also returns false if query was null.
   */
  bool getUnsatCore(SmtEngine& smt,
                    Node query,
                    std::vector<Node>& uasserts) const;
  /**
   * Return the result of checking satisfiability of formula n.
   * If n was satisfiable, then we store the model for d_vars in mvs.
   */
  Result checkSat(Node n, std::vector<Node>& mvs) const;
  //-----------------------------------end for SMT engine calls
  //-----------------------------------for evaluation
  /**
   * Return the evaluation of n under the substitution { d_vars -> mvs }.
   * If id is non-null, then id is a unique identifier for mvs, and we cache
   * the result of n for this point.
   */
  Node evaluate(Node n, Node id, const std::vector<Node>& mvs);
  /** A cache of the above function */
  std::unordered_map<Node,
                     std::unordered_map<Node, Node, NodeHashFunction>,
                     NodeHashFunction>
      d_eval_cache;
  /** The evaluator utility used for the above function */
  Evaluator d_eval;
  //-----------------------------------end for evaluation

  /** Construct solution from pool
   *
   * This is the main body of the core connective algorithm, which attempts
   * to build a solution based on one direction (pre/post) of the synthesis
   * conjecture.
   *
   * It takes as input:
   * - a component ccheck that maintains information regarding the direction
   * we are trying to build a solution for,
   * - the current set of assertions asserts that comprise the current solution
   * we are building,
   * - the current pool passerts of available assertions that we may add to
   * asserts.
   */
  Node constructSolutionFromPool(Component& ccheck,
                                 std::vector<Node>& asserts,
                                 std::vector<Node>& passerts);

  class Stats
  {
   public:
    void reset();
    unsigned d_evals;
    unsigned d_coreCheck;
    unsigned d_addLits;
    unsigned d_maxLits;
  };
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
