/*********************                                                        */
/*! \file cegis_core_connective.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
 * A trie that stores data at undetermined depth. Storing data at
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
 * exists P. forall x. (A[x] => C(x)) ^ (C(x) => B(x))
 * That is, conjectures with a pre/post condition but no inductive relation
 * or other constraints. Additionally, we may have that the above conjecture
 * has a side condition SC, which requires that exists x. SC[x]^C(x) is
 * satisfiable.
 *
 * Two examples of this kind of sygus conjecture are abduction and
 * interpolation.
 *
 * This module implements a specific algorithm for constructing solutions
 * to this conjecture based on Boolean connectives and unsat cores, described
 * in following. We give two variants of the algorithm, both implemented as
 * special cases of this class. Below, let:
 *
 * pool(A) be a set of literals { c_1, ..., c_n } s.t. c_i => B for i=1,...,n,
 * pts(A) : a set of points { v | A[v] is true },
 * pool(B) : a set of literals { d_1, ..., d_m } s.t. A => d_i for i=1,...,m,
 * pts(B) : a set of points { v | ~B[v] is true },
 * cores(B) : a set of sets of literals { U_1, ..., U_p } s.t. for i=1,...,p:
 * - U_i is a subset of pool(B),
 * - A ^ U_i is unsat.
 * We construct pool(A)/pool(B) using enumerative SyGuS, discarding the literals
 * that do not match the criteria.
 *
 * Variant #1 (Interpolation)
 *
 * Let the synthesis conjecture be of the form
 *   exists C. forall x. A[x] => C[x] ^ C[x] => B[x]
 *
 * The high level idea is we construct solutions for C of the form
 *   c_1 OR ... OR c_n where c_i => B for each i=1,...,n, or
 *   d_1 AND ... AND d_m where A => d_i for each i=1,...,m.
 *
 * while(true){
 *   Let e_i = next_sygus_enum();
 *   // check if e_i should be added to pool(B)
 *   if e_i[v] is true for all v in pts(A)
 *     if A => e_i
 *       pool(B) += e_i;
 *     else
 *       pts(A) += { v } where { x -> v } is a model for A ^ ~e_i;
 *   // try to construct a solution based on the pool
 *   Let D = {}.
 *   while
 *     D[v] is true for some v in pts(B), and
 *     d'[v] is false for some d' in pool(B)
 *   {
 *     D += { d' }
 *     if D is false for all v in pts(B)
 *       if D => B
 *         return AND_{d in D}( d )
 *       else
 *         pts(B) += { v } where { x -> v } is a model for D ^ ~B
 *   }
 *
 *   // analogous for the other direction
 * }
 *
 *
 * Variant #2 (Abduction)
 *
 * Let the synthesis conjecture be of the form exists C. forall x. C[x] => B[x]
 * such that S[x] ^ C[x] is satisfiable. We refer to S as the side condition
 * for this conjecture. Notice that A in this variant is false, hence the
 * algorithm below is modified accordingly.
 *
 * The high level idea is we construct solutions for C of the form
 *   d_1 AND ... AND d_n
 * where the above conjunction is weakened based on only including conjuncts
 * that are in the unsat core of d_1 AND ... AND d_n => B.
 *
 * while(true){
 *   Let e_i = next_sygus_enum();
 *   // add e_i to the pool
 *   pool(B) += e_i;
 *   // try to construct a solution based on the pool
 *   Let D = {}.
 *   while
 *     D[v] is true for some v in pts(B), and
 *     d'[v] is false for some d' in pool(B) and
 *     no element of cores(B) is a subset of D ++ { d' }
 *   {
 *     D += { d' }
 *     if D is false for all v in pts(B)
 *       if (S ^ D) => B
 *         Let U be a subset of D such that S ^ U ^ ~B is unsat.
 *         if S ^ U is unsat
 *           Let W be a subset of D such that S ^ W is unsat.
 *             cores(B) += W
 *             remove some d'' in W from D
 *         else
 *           return u_1 AND ... AND u_m where U = { u_1, ..., u_m }
 *       else
 *         pts(B) += { v } where { x -> v } is a model for D ^ ~B
 *   }
 * }
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
    Component() : d_numFalseCores(0), d_numRefPoints(0) {}
    /** initialize
     *
     * This initializes this component with pre/post condition given by n
     * and sygus constructor c.
     */
    void initialize(Node n, Node c);
    /** get the formula n that we initialized this with */
    Node getFormula() const { return d_this; }
    /** Is this component active? */
    bool isActive() const { return !d_scons.isNull(); }
    /** Add term n to pool whose sygus analog is s */
    void addToPool(Node n, Node s);
    /** Add a refinement point to this component */
    void addRefinementPt(Node id, const std::vector<Node>& pt);
    /** Add a false case to this component */
    void addFalseCore(Node id, const std::vector<Node>& u);
    /**
     * Selects a node from passerts that evaluates to false on point mv if one
     * exists, or otherwise returns false.
     * The argument mvId is an identifier used for indexing the point mv.
     * The argument asserts stores the current candidate solution (set D in
     * Variant #2 described above). If the method returns true, it updates
     * an (the node version of asserts) to be the conjunction of the nodes
     * in asserts.
     *
     * If true is returned, it is removed from passerts.
     */
    bool addToAsserts(CegisCoreConnective* p,
                      std::vector<Node>& passerts,
                      const std::vector<Node>& mvs,
                      Node mvId,
                      std::vector<Node>& asserts,
                      Node& an);

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
    /** Get term pool, i.e. pool(A)/pool(B) in the algorithms above */
    void getTermPool(std::vector<Node>& passerts) const;
    /**
     * Get the sygus solution corresponding to the Boolean connective for
     * this component applied to conj. In particular, this returns a
     * right-associative chain of applications of sygus constructor d_scons
     * to the sygus analog of formulas in conj.
     */
    Node getSygusSolution(std::vector<Node>& conjs) const;
    /** debug print summary (for debugging) */
    void debugPrintSummary(std::ostream& os) const;

   private:
    /** The original formula for the pre/post condition A/B. */
    Node d_this;
    /**
     * The sygus constructor for constructing solutions based on the core
     * connective algorithm. This is a sygus datatype constructor that
     * encodes applications of AND or OR.
     */
    Node d_scons;
    /** This is pool(A)/pool(B) in the algorithms above */
    std::vector<Node> d_cpool;
    /**
     * A map from the formulas in the above vector to their sygus analog.
     */
    std::map<Node, Node> d_cpoolToSol;
    /**
     * An index of list of predicates such that each list ( P1, ..., Pn )
     * indexed by this trie is such that P1 ^ ... ^ Pn ^ S is unsatisfiable,
     * where S is the side condition of our synthesis conjecture. We call this
     * a "false core". This set is "cores(B)" in Variant #2 above.
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
   * Assuming smt has just been called to check-sat and returned "UNSAT", this
   * method get the unsat core and adds it to uasserts.
   *
   * The assertions in the argument queryAsserts (which we are not interested
   * in tracking in the unsat core) are excluded from uasserts.
   * If one of the formulas in queryAsserts was in the unsat core, then this
   * method returns true. Otherwise, this method returns false.
   */
  bool getUnsatCore(
      SmtEngine& smt,
      const std::unordered_set<Node, NodeHashFunction>& queryAsserts,
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
   *
   * This implements the while loop in the algorithms above. If this method
   * returns a non-null node, then this is a solution for the given synthesis
   * conjecture.
   */
  Node constructSolutionFromPool(Component& ccheck,
                                 std::vector<Node>& asserts,
                                 std::vector<Node>& passerts);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
