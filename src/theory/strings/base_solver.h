/*********************                                                        */
/*! \file base_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base solver for term indexing and constant inference for the
 ** theory of strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__BASE_SOLVER_H
#define CVC4__THEORY__STRINGS__BASE_SOLVER_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** The base solver for the theory of strings
 *
 * This implements techniques for inferring when terms are congruent in the
 * current context, and techniques for inferring when equivalence classes
 * are equivalent to constants.
 */
class BaseSolver
{
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  BaseSolver(context::Context* c,
             context::UserContext* u,
             SolverState& s,
             InferenceManager& im);
  ~BaseSolver();

  //-----------------------inference steps
  /** check initial
   *
   * This function initializes term indices for each strings function symbol.
   * One key aspect of this construction is that concat terms are indexed by
   * their list of non-empty components. For example, if x = "" is an equality
   * asserted in this SAT context, then y ++ x ++ z may be indexed by (y,z).
   * This method may infer various facts while building these term indices, for
   * instance, based on congruence. An example would be inferring:
   *   y ++ x ++ z = y ++ z
   * if both terms are registered in this SAT context.
   *
   * This function should be called as a first step of any strategy.
   */
  void checkInit();
  /** check constant equivalence classes
   *
   * This function infers whether CONCAT terms can be simplified to constants.
   * For example, if x = "a" and y = "b" are equalities in the current SAT
   * context, then we may infer x ++ "c" ++ y is equivalent to "acb". In this
   * case, we infer the fact x ++ "c" ++ y = "acb".
   */
  void checkConstantEquivalenceClasses();
  /** check cardinality
   *
   * This function checks whether a cardinality inference needs to be applied
   * to a set of equivalence classes. For details, see Step 5 of the proof
   * procedure from Liang et al, CAV 2014.
   */
  void checkCardinality();
  //-----------------------end inference steps

  //-----------------------query functions
  /**
   * Is n congruent to another term in the current context that has not been
   * marked congruent? If so, we can ignore n.
   *
   * Note this and the functions in this block below are valid during a full
   * effort check after a call to checkInit.
   */
  bool isCongruent(Node n);
  /**
   * Get the constant that the equivalence class eqc is entailed to be equal
   * to, or null if none exist.
   */
  Node getConstantEqc(Node eqc);
  /**
   * Same as above, where the explanation for n = c is added to exp if c is
   * the (non-null) return value of this function, where n is a term in the
   * equivalence class of eqc.
   */
  Node explainConstantEqc(Node n, Node eqc, std::vector<Node>& exp);
  /**
   * Get the set of equivalence classes of type string.
   */
  const std::vector<Node>& getStringEqc() const;
  //-----------------------end query functions

 private:
  /**
   * A term index that considers terms modulo flattening and constant merging
   * for concatenation terms.
   */
  class TermIndex
  {
   public:
    /** Add n to this trie
     *
     * A term is indexed by flattening arguments of concatenation terms,
     * and replacing them by (non-empty) constants when possible, for example
     * if n is (str.++ x y z) and x = "abc" and y = "" are asserted, then n is
     * indexed by ("abc", z).
     *
     * index: the child of n we are currently processing,
     * s : reference to solver state,
     * er : the representative of the empty equivalence class.
     *
     * We store the vector of terms that n was indexed by in the vector c.
     */
    Node add(TNode n,
             unsigned index,
             const SolverState& s,
             Node er,
             std::vector<Node>& c);
    /** Clear this trie */
    void clear() { d_children.clear(); }
    /** The data at this node of the trie */
    Node d_data;
    /** The children of this node of the trie */
    std::map<TNode, TermIndex> d_children;
  };
  /**
   * This method is called as we are traversing the term index ti, where vecc
   * accumulates the list of constants in the path to ti. If ti has a non-null
   * data n, then we have inferred that d_data is equivalent to the
   * constant specified by vecc.
   */
  void checkConstantEquivalenceClasses(TermIndex* ti, std::vector<Node>& vecc);
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Commonly used constants */
  Node d_emptyString;
  Node d_false;
  /**
   * A congruence class is a set of terms f( t1 ), ..., f( tn ) where
   * t1 = ... = tn. Congruence classes are important since all but
   * one of the above terms (the representative of the congruence class)
   * can be ignored by the solver.
   *
   * This set contains a set of nodes that are not representatives of their
   * congruence class. This set is used to skip reasoning about terms in
   * various inference schemas implemnted by this class.
   */
  NodeSet d_congruent;
  /**
   * The following three vectors are used for tracking constants that each
   * equivalence class is entailed to be equal to.
   * - The map d_eqcToConst maps (representatives) r of equivalence classes to
   * the constant that that equivalence class is entailed to be equal to,
   * - The term d_eqcToConstBase[r] is the term in the equivalence class r
   * that is entailed to be equal to the constant d_eqcToConst[r],
   * - The term d_eqcToConstExp[r] is the explanation of why
   * d_eqcToConstBase[r] is equal to d_eqcToConst[r].
   *
   * For example, consider the equivalence class { r, x++"a"++y, x++z }, and
   * assume x = "" and y = "bb" in the current context. We have that
   *   d_eqcToConst[r] = "abb",
   *   d_eqcToConstBase[r] = x++"a"++y
   *   d_eqcToConstExp[r] = ( x = "" AND y = "bb" )
   *
   * This information is computed during checkInit and is used during various
   * inference schemas for deriving inferences.
   */
  std::map<Node, Node> d_eqcToConst;
  std::map<Node, Node> d_eqcToConstBase;
  std::map<Node, Node> d_eqcToConstExp;
  /** The list of equivalence classes of type string */
  std::vector<Node> d_stringsEqc;
  /** A term index for each function kind */
  std::map<Kind, TermIndex> d_termIndex;
  /** the cardinality of the alphabet */
  uint32_t d_cardSize;
  /** The string-like type for this base solver */
  TypeNode d_type;
}; /* class BaseSolver */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__BASE_SOLVER_H */
