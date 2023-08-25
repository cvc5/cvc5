/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base solver for term indexing and constant inference for the
 * theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__BASE_SOLVER_H
#define CVC5__THEORY__STRINGS__BASE_SOLVER_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/** The base solver for the theory of strings
 *
 * This implements techniques for inferring when terms are congruent in the
 * current context, and techniques for inferring when equivalence classes
 * are equivalent to constants.
 */
class BaseSolver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  BaseSolver(Env& env, SolverState& s, InferenceManager& im, TermRegistry& tr);
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
  enum class CardinalityResponse
  {
    // we don't have to check cardinality for the given type
    NO_REQ,
    // we have to check cardinality
    REQ,
    // we don't know how to check cardinality
    UNHANDLED
  };
  /**
   * Get the cardinality requirement for type tn, which is either:
   * - NO_REQ, meaning there is no restriction on the number of equivalence
   * classes for tn,
   * - REQ, meaning we have a finite cardinality based on which we need to
   * check cardinality for. In this case, typeCardSize is set of the cardinality
   * of tn.
   * - UNHANDLED, meaning we don't know how to handle cardinality for tn, in
   * which case model construction is not guaranteed to succeed.
   */
  CardinalityResponse getCardinalityReq(TypeNode tn,
                                        size_t& typeCardSize) const;
  /**
   * If there are eqcCount equivalence classes of a type with fixed cardinality
   * typeCardSize all having length lr, this returns false if we have to
   * add a cardinality inference.
   *
   * If this method returns false, then lenNeed is set to the length that
   * is required for the equivalence classes to have.
   */
  bool isCardinalityOk(size_t typeCardSize,
                       Node lr,
                       size_t eqcCount,
                       size_t& lenNeed) const;
  /** Same as above, without tracking lenNeed. */
  bool isCardinalityOk(size_t typeCardSize, Node lr, size_t eqcCount) const;
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
   * Same as above, for "best content" terms.
   */
  Node explainBestContentEqc(Node n, Node eqc, std::vector<Node>& exp);
  /**
   * Get the set of equivalence classes of type string.
   */
  const std::vector<Node>& getStringLikeEqc() const;
  //-----------------------end query functions

 private:
  /**
   * The information that we associated with each equivalence class.
   *
   * Example 1. Consider the equivalence class { r, x++"a"++y, x++z }, and
   * assume x = "" and y = "bb" in the current context. We have that
   *   d_bestContent = "abb",
   *   d_base = x++"a"++y
   *   d_exp = ( x = "" AND y = "bb" )
   *
   * Example 2. Consider the equivalence class { r, x++"a"++w++y, x++z }, and
   * assume x = "" and y = "bb" in the current context. We have that
   *   d_bestContent = "a" ++ w ++ "bb",
   *   d_bestScore = 3
   *   d_base = x++"a"++w++y
   *   d_exp = ( x = "" AND y = "bb" )
   *
   * This information is computed during checkInit and is used during various
   * inference schemas for deriving inferences.
   */
  struct BaseEqcInfo
  {
    /**
     * Either a constant or a concatentation of constants and variables that
     * this equivalence class is entailed to be equal to. If it is a
     * concatenation, this is the concatenation that is currently known to have
     * the highest score (see `d_bestScore`).
     */
    Node d_bestContent;
    /**
     * The sum of the number of characters in the string literals of
     * `d_bestContent`.
     */
    size_t d_bestScore;
    /**
     * The term in the equivalence class that is entailed to be equal to
     * `d_bestContent`.
     */
    Node d_base;
    /** This term explains why `d_bestContent` is equal to `d_base`. */
    Node d_exp;
  };

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
     * overwrite : if this is set to true then an existing element at the same
     *             index is updated to `n`
     *
     * We store the vector of terms that n was indexed by in the vector c.
     */
    Node add(TNode n,
             unsigned index,
             const SolverState& s,
             Node er,
             bool overwrite,
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
   *
   * @param ti The term index for string concatenations
   * @param vecc The list of constants in the path to ti
   * @param ensureConst If true, require that each element in the path is
   *                    constant
   * @param isConst If true, the path so far only includes constants
   */
  void checkConstantEquivalenceClasses(TermIndex* ti,
                                       std::vector<Node>& vecc,
                                       bool ensureConst = true,
                                       bool isConst = true);
  /**
   * Check cardinality for type tn. This adds a lemma corresponding to
   * cardinality for terms of type tn, if applicable.
   *
   * @param tn The string-like type of terms we are considering,
   * @param cols The list of collections of equivalence classes. This is a
   * partition of all string equivalence classes, grouped by those with equal
   * lengths.
   * @param lts The length of each of the collections in cols.
   */
  void checkCardinalityType(TypeNode tn,
                            std::vector<std::vector<Node> >& cols,
                            std::vector<Node>& lts);
  /**
   * Called when a and b are constant-like terms in the same equivalence class.
   *
   * @return true if a conflict was discovered
   */
  bool processConstantLike(Node a, Node b);
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
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
   * various inference schemas implemented by this class.
   */
  NodeSet d_congruent;
  /**
   * Set of equalities that we have applied STRINGS_UNIT_INJ_OOB to
   * in the current user context
   */
  NodeSet d_strUnitOobEq;
  /**
   * Maps equivalence classes to their info, see description of `BaseEqcInfo`
   * for more information.
   */
  std::map<Node, BaseEqcInfo> d_eqcInfo;
  /** The list of equivalence classes of string-like types */
  std::vector<Node> d_stringLikeEqc;
  /** A term index for each type, function kind pair */
  std::map<TypeNode, std::map<Kind, TermIndex> > d_termIndex;
  /** the cardinality of the alphabet */
  uint32_t d_cardSize;
}; /* class BaseSolver */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__BASE_SOLVER_H */
