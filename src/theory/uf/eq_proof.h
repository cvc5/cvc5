/*********************                                                        */
/*! \file eq_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof as produced by the equality engine.
 **
 **/

#include "cvc4_private.h"
#include "expr/node.h"
#include "theory/uf/equality_engine_types.h"

namespace CVC4 {

class CDProof;

namespace theory {
namespace eq {

/**
 * An equality proof.
 *
 * This represents the reasoning performed by the Equality Engine to derive
 * facts, represented in terms of the rules in MergeReasonType. Each proof step
 * is annotated with the rule id, the conclusion node and a vector of proofs of
 * the rule's premises.
 **/
class EqProof
{
 public:
  EqProof() : d_id(MERGED_THROUGH_REFLEXIVITY) {}
  /** The proof rule for concluding d_node */
  MergeReasonType d_id;
  /** The conclusion of this EqProof */
  Node d_node;
  /** The proofs of the premises for deriving d_node with d_id */
  std::vector<std::shared_ptr<EqProof>> d_children;
  /**
   * Debug print this proof on debug trace c with tabulation tb.
   */
  void debug_print(const char* c, unsigned tb = 0) const;
  /**
   * Debug print this proof on output stream os with tabulation tb.
   */
  void debug_print(std::ostream& os, unsigned tb = 0) const;

  /** Add to proof
   *
   * Converts EqProof into ProofNode via a series of steps to be stored in
   * CDProof* p.
   *
   * This method can be seen as a best-effort solution until the EqualityEngine
   * is updated to produce ProofNodes directly, if ever. Note that since the
   * original EqProof steps can be coarse-grained (e.g. without proper order,
   * implicit inferences related to disequelaties) and are phrased over curried
   * terms, the transformation requires significant, although cheap (mostly
   * linear on the DAG-size of EqProof), post-processing.
   *
   * An important invariant of the resulting ProofNode is that neither its
   * assumptions nor its conclusion are predicate equalities, i.e. of the form
   * (= t true/false), modulo symmetry. This is so that users of the converted
   * ProofNode don't need to do case analysis on whether assumptions/conclusion
   * are either t or (= t true/false).
   *
   * @param p a pointer to a CDProof to store the conversion of this EqProof
   * @return the node that is the conclusion of the proof as added to p.
   */
  Node addToProof(CDProof* p) const;

 private:
  /**
   * As above, but with a cache of previously processed nodes and their results
   * (for DAG traversal). The caching is in terms of the original conclusions of
   * EqProof.
   *
   * @param p a pointer to a CDProof to store the conversion of this EqProof
   * @param visited a cache of the original EqProof conclusions and the
   * resulting conclusion after conversion.
   * @param assumptions the assumptions of the original EqProof (and their
   * variations in terms of symmetry and conversion to/from predicate
   * equalities)
   * @return the node that is the conclusion of the proof as added to p.
   */
  Node addToProof(
      CDProof* p,
      std::unordered_map<Node, Node, NodeHashFunction>& visited,
      std::unordered_set<Node, NodeHashFunction>& assumptions) const;

  /** Removes all reflexivity steps, i.e. (= t t), from premises. */
  void cleanReflPremises(std::vector<Node>& premises) const;

  /** Expand coarse-grained transitivity steps for disequalities
   *
   * Currently the equality engine can represent disequality reasoning in a
   * rather coarse-grained manner with EqProof. This is always the case when the
   * transitivity step contains a disequality, (= (= t t') false) or its
   * symmetric, as a premise.
   *
   * There are two cases. In the simplest one the general shape of the EqProof
   * is
   *  (= t1 t2) (= t3 t2) (= (t1 t3) false)
   *  ------------------------------------- EQP::TR
   *             false = true
   *
   * which is expanded into
   *                                          (= t3 t2)
   *                                          --------- SYMM
   *                                (= t1 t2) (= t2 t3)
   *                                ------------------- TRANS
   *   (= (= t1 t3) false)                (= t1 t3)
   *  --------------------- SYMM    ------------------ TRUE_INTRO
   *   (= false (= t1 t3))         (= (= t1 t3) true)
   *  ----------------------------------------------- TRANS
   *             false = true
   *
   * by explicitly adding the transitivity step for inferring (= t1 t3) and its
   * predicate equality. Note that we differentiate (from now on) the EqProof
   * rules ids from those of ProofRule by adding the prefix EQP:: to the former.
   *
   * In the other case, the general shape of the EqProof is
   *
   *  (= (= t1 t2) false) (= t1 x1) ... (= xn t3) (= t2 y1) ... (= ym t4)
   * ------------------------------------------------------------------- EQP::TR
   *         (= (= t4 t3) false)
   *
   * which is converted into
   *
   *   (= t1 x1) ... (= xn t3)      (= t2 y1) ... (= ym t4)
   *  ------------------------ TR  ------------------------ TR
   *   (= t1 t3)                    (= t2 t4)
   *  ----------- SYMM             ----------- SYMM
   *   (= t3 t1)                    (= t4 t2)
   *  ---------------------------------------- CONG
   *   (= (= t3 t4) (= t1 t2))                         (= (= t1 t2) false)
   *  --------------------------------------------------------------------- TR
   *           (= (= t3 t4) false)
   *          --------------------- MACRO_SR_PRED_TRANSFORM
   *           (= (= t4 t3) false)
   *
   * whereas the last step is only necessary if the conclusion has the arguments
   * in reverse order than expected. Note that the original step represents two
   * substitutions happening on the disequality, from t1->t3 and t2->t4, which
   * are implicitly justified by transitivity steps that need to be made
   * explicity. Since there is no sense of ordering among which premisis (other
   * than (= (= t1 t2) false)) are used for which substitution, the transitivity
   * proofs are built greedly by searching the sets of premises.
   *
   * If in either of the above cases then the conclusion is directly derived
   * in the call, so only in the other cases we try to build a transitivity
   * step below
   *
   * @param conclusion the conclusion of the (possibly) coarse-grained
   * transitivity step
   * @param premises the premises of the (possibly) coarse-grained
   * transitivity step
   * @param p a pointer to a CDProof to store the conversion of this EqProof
   * @param assumptions the assumptions (and variants) of the original
   * EqProof. These are necessary to avoid cyclic proofs, which could be
   * generated by creating transitivity steps for assumptions (which depend on
   * themselves).
   * @return True if the EqProof transitivity step is in either of the above
   * cases, symbolizing that the ProofNode justifying the conclusion has already
   * been produced.
   */
  bool expandTransitivityForDisequalities(
      Node conclusion,
      std::vector<Node>& premises,
      CDProof* p,
      std::unordered_set<Node, NodeHashFunction>& assumptions) const;

  /** Expand coarse-grained transitivity steps for theory disequalities
   *
   * Currently the equality engine can represent disequality reasoning of theory
   * symbols in a rather coarse-grained manner with EqProof. This is the case
   * when EqProof is
   *            (= t1 c1) (= t2 c2)
   *  ------------------------------------- EQP::TR
   *             (= (t1 t2) false)
   *
   * which is converted into
   *
   *   (= t1 c1)        (= t2 c2)
   *  -------------------------- CONG  --------------------- MACRO_SR_PRED_INTRO
   *   (= (= t1 t2) (= c1 t2))           (= (= c1 c2) false)
   *  --------------------------------------------------------- TR
   *           (= (= t1 t2) false)
   *
   * @param conclusion the conclusion of the (possibly) coarse-grained
   * transitivity step
   * @param premises the premises of the (possibly) coarse-grained
   * transitivity step
   * @param p a pointer to a CDProof to store the conversion of this EqProof
   * @return True if the EqProof transitivity step is the above case,
   * indicating that the ProofNode justifying the conclusion has already been
   * produced.
   */
  bool expandTransitivityForTheoryDisequalities(Node conclusion,
                                                std::vector<Node>& premises,
                                                CDProof* p) const;

  /** Builds a transitivity chain from equalities to derive a conclusion
   *
   * Given an equality (= t1 tn), and a list of equalities premises, attempts to
   * build a chain (= t1 t2) ... (= tn-1 tn) from premises. This is done in a
   * greedy manner by finding one "link" in the chain at a time, updating the
   * conclusion to be the next link and the premises by removing the used
   * premise, and searching recursively.
   *
   * Consider for example
   * - conclusion: (= t1 t4)
   * - premises:   (= t4 t2), (= t2 t3), (= t2 t1), (= t3 t4)
   *
   * It proceeds by searching for t1 in an equality in the premises, in order,
   * which is found in the equality (= t2 t1). Since t2 != t4, it attempts to
   * build a chain with
   * - conclusion (= t2 t4)
   * - premises (= t4 t2), (= t2 t3), (= t3 t4)
   *
   * In the first equality it finds t2 and also t4, which closes the chain, so
   * that premises is updated to (= t2 t4) and the method returns true. Since
   * the recursive call was successful, the original conclusion (= t1 t4) is
   * justified with (= t1 t2) plus the chain built in the recursive call,
   * i.e. (= t1 t2), (= t2 t4).
   *
   * Note that not all the premises were necessary to build a successful
   * chain. Moreover, note that building a successful chain can depend on the
   * order in which the equalities are chosen. When a recursive call fails to
   * close a chain, the chosen equality is dismissed and another is searched for
   * among the remaining ones.
   *
   * This method assumes that premises does not contain reflexivity premises.
   * This is without loss of generality since such premises are spurious for a
   * transitivity step.
   *
   * @param conclusion the conclusion of the transitivity chain of equalities
   * @param premises the list of equalities to build a chain with
   * @return whether premises successfully build a transitivity chain for the
   * conclusion
   */
  bool buildTransitivityChain(Node conclusion,
                              std::vector<Node>& premises) const;

  /** Reduce the a congruence EqProof into a transitivity matrix
   *
   * Given a congruence EqProof of (= (f a0 ... an-1) (f b0 ... bn-1)), reduce
   * its justification into a matrix
   *
   *   [0]   -> p_{0,0} ... p_{m_0,0}
   *   ...
   *   [n-1] -> p_{0,n} ... p_{m_n-1,n-1}
   *
   * where f has arity n and each p_{0,i} ... p_{m_i, i} is a transitivity chain
   * (modulo ordering) justifying (= ai bi).
   *
   * Congruence steps in EqProof are binary, representing reasoning over curried
   * applications. In the simplest case the general shape of a congruence
   * EqProof is:
   *                                     P0
   *              ------- EQP::REFL  ----------
   *       P1        []               (= a0 b0)
   *  ---------   ----------------------- EQP::CONG
   *  (= a1 b1)             []                        P2
   *  ------------------------- EQP::CONG        -----------
   *             []                               (= a2 b2)
   *          ------------------------------------------------ EQP::CONG
   *                  (= (f a0 a1 a2) (f b0 b1 b2))
   *
   * where [] stands for the null node, symbolizing "equality between partial
   * applications".
   *
   * The reduction of such a proof is done by
   * - converting the proof of the second CONG premise (via addToProof) and
   *   adding the resulting node to row i of the matrix
   * - recursively reducing the first proof with i-1
   *
   * In the above case the transitivity matrix would thus be
   *   [0] -> (= a0 b0)
   *   [1] -> (= a1 b1)
   *   [2] -> (= a2 b2)
   *
   * The more complex case of congruence proofs has transitivity steps as the
   * first child of CONG steps. For example
   *                                     P0
   *              ------- EQP::REFL  ----------
   *     P'          []            (= a0 c)
   *  ---------   ----------------------------- EQP::CONG
   *  (= b0 c)             []                               P1
   * ------------------------- EQP::TRANS             -----------
   *            []                                     (= a1 b1)
   *         ----------------------------------------------------- EQP::CONG
   *                          (= (f a0 a1) (f b0 b1))
   *
   * where when the first child of CONG is a transitivity step
   * - the premises that are CONG steps are recursively reduced with *the same*
       argument i
   * - the other premises are processed with addToProof and added to the i row
   *   in the matrix
   *
   * In the above example the to which the transitivity matrix is
   *   [0] -> (= a0 c), (= b0 c)
   *   [1] -> (= a1 b1)
   *
   * The remaining complication is that when conclusion is an equality of n-ary
   * applications of *different* arities, there is, necessarily, a transitivity
   * step as a first child a CONG step whose conclusion is an equality of n-ary
   * applications of different arities. For example
   *             P0                              P1
   * -------------------------- EQP::TRANS  -----------
   *     (= (f a0 a1) (f b0))                (= a2 b1)
   * -------------------------------------------------- EQP::CONG
   *              (= (f a0 a1 a2) (f b0 b1))
   *
   * will be first reduced with i = 2 (maximal arity amorg the original
   * conclusion's applications), adding (= a2 b1) to row 2 after processing
   * P1. The first child is reduced with i = 1. Since it is a TRANS step whose
   * conclusion is an equality of n-ary applications with mismatching arity, P0
   * is processed with addToProof and the result is added to row 1. Thus the
   * transitivity matrix is
   *   [0] ->
   *   [1] -> (= (f a0 a1) (f b0))
   *   [2] -> (= a2 b1)
   *
   * The empty row 0 is used by the original caller of reduceNestedCongruence to
   * compute that the above congruence proof's conclusion is
   *   (= (f (f a0 a1) a2) (f (f b0) b1))
   *
   * @param i the i-th argument of the congruent applications, initially being
   * the maximal arity among conclusion's applications.
   * @param conclusion the original congruence conclusion
   * @param transitivityMatrix a matrix of equalities with each row justifying
   * an equality between the congruent applications
   * @param p a pointer to a CDProof to store the conversion of this EqProof
   * @param visited a cache of the original EqProof conclusions and the
   * resulting conclusion after conversion.
   * @param assumptions the assumptions (and variants) of the original EqProof
   * @param isNary whether conclusion is an equality of n-ary applications
   */
  void reduceNestedCongruence(
      unsigned i,
      Node conclusion,
      std::vector<std::vector<Node>>& transitivityMatrix,
      CDProof* p,
      std::unordered_map<Node, Node, NodeHashFunction>& visited,
      std::unordered_set<Node, NodeHashFunction>& assumptions,
      bool isNary) const;

}; /* class EqProof */

}  // Namespace eq
}  // Namespace theory
}  // Namespace CVC4
