/*********************                                                        */
/*! \file ho_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The higher-order extension of TheoryUF.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__HO_EXTENSION_H
#define __CVC4__THEORY__UF__HO_EXTENSION_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF;

/** The higher-order extension of the theory of uninterpreted functions
 *
 * This extension is capable of handling UF constraints involving partial
 * applications via the applicative encoding (kind HO_APPLY), and
 * (dis)equalities involving function sorts. It uses a lazy applicative
 * encoding and implements two axiom schemes, at a high level:
 *
 * (1) Extensionality, where disequalities between functions witnessed by
 * arguments where the two functions differ,
 *
 * (2) App-Encode, where full applications of UF (kind APPLY_UF) are equated
 * with curried applications (kind HO_APPLY).
 *
 * For more details, see "Extending SMT Solvers to Higher-Order", Barbosa et al.
 */
class HoExtension
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

 public:
  HoExtension(TheoryUF& p, context::Context* c, context::UserContext* u);

  /** expand definition
   *
   * This returns the expanded form of node.
   *
   * In particular, this function will convert applications of HO_APPLY
   * to applications of APPLY_UF if they are fully applied, and introduce
   * function variables for function heads that are not variables via the
   * getApplyUfForHoApply method below.
   */
  Node expandDefinition(Node node);

  /** check higher order
   *
   * This is called at full effort and infers facts and sends lemmas
   * based on higher-order reasoning (specifically, extentionality and
   * app completion). It returns the number of lemmas plus facts
   * added to the equality engine.
   */
  unsigned check();

  /** applyExtensionality
   *
   * Given disequality deq f != g, if not already cached, this sends a lemma of
   * the form:
   *   f = g V (f k) != (g k) for fresh constant k on the output channel of the
   * parent TheoryUF object. This is an "extensionality lemma".
   * Return value is the number of lemmas of this form sent on the output
   * channel.
   */
  unsigned applyExtensionality(TNode deq);

  /** collect model info
   *
   * This method adds the necessary equalities to the model m such that
   * model construction is possible if this method returns true. These
   * equalities may include HO_APPLY versions of all APPLY_UF terms.
   *
   * The argument termSet is the set of relevant terms that the parent TheoryUF
   * object has added to m that belong to TheoryUF.
   *
   * This method ensures that the function variables in termSet
   * respect extensionality. If some pair does not, then this method adds an
   * extensionality equality directly to the equality engine of m.
   *
   * In more detail, functions f and g do not respect extensionality if f and g
   * are not equal in the model, and there is not a pair of unequal witness
   * terms f(k), g(k). In this case, we add the disequality
   *    f(k') != g(k')
   * for fresh (tuple) of variables k' to the equality engine of m. Notice
   * this is done only for functions whose type has infinite cardinality,
   * since all functions with finite cardinality are ensured to respect
   * extensionality by this point due to our extentionality inference schema.
   *
   * If this method returns true, then all pairs of functions that are in
   * distinct equivalence classes will be guaranteed to be assigned different
   * values in m. It returns false if any (dis)equality added to m led to
   * an inconsistency in m.
   */
  bool collectModelInfoHo(std::set<Node>& termSet, TheoryModel* m);

 protected:
  /** get apply uf for ho apply
   *
   * This returns the APPLY_UF equivalent for the HO_APPLY term node, where
   * node has non-functional return type (that is, it corresponds to a fully
   * applied function term).
   * This call may introduce a skolem for the head operator and send out a lemma
   * specifying the definition.
   */
  Node getApplyUfForHoApply(Node node);

  /** get extensionality disequality
   *
   * Given disequality deq f != g, this returns the disequality:
   *   (f k) != (g k) for fresh constant(s) k.
   *
   * If isCached is true, then this returns the same k for all calls to this
   * method with the same deq. If it is false, it creates fresh k and does not
   * cache the result.
   */
  Node getExtensionalityDeq(TNode deq, bool isCached = true);

  /**
   * Check whether extensionality should be applied for any pair of terms in the
   * equality engine.
   *
   * If we pass a null model m to this function, then we add extensionality
   * lemmas to the output channel and return the total number of lemmas added.
   * We only add lemmas for functions whose type is finite, since pairs of
   * functions whose types are infinite can be made disequal in a model by
   * witnessing a point they are disequal.
   *
   * If we pass a non-null model m to this function, then we add disequalities
   * that correspond to the conclusion of extensionality lemmas to the model's
   * equality engine. We return 0 if the equality engine of m is consistent
   * after this call, and 1 otherwise. We only add disequalities for functions
   * whose type is infinite, since our decision procedure guarantees that
   * extensionality lemmas are added for all pairs of functions whose types are
   * finite.
   */
  unsigned checkExtensionality(TheoryModel* m = nullptr);

  /** applyAppCompletion
   * This infers a correspondence between APPLY_UF and HO_APPLY
   * versions of terms for higher-order.
   * Given APPLY_UF node e.g. (f a b c), this adds the equality to its
   * HO_APPLY equivalent:
   *   (f a b c) == (@ (@ (@ f a) b) c)
   * to equality engine, if not already equal.
   * Return value is the number of equalities added.
   */
  unsigned applyAppCompletion(TNode n);

  /** check whether app-completion should be applied for any
   * pair of terms in the equality engine.
   */
  unsigned checkAppCompletion();
  /** collect model info for higher-order term
   *
   * This adds required constraints to m for term n. In particular, if n is
   * an APPLY_UF term, we add its HO_APPLY equivalent in this call. We return
   * true if the model m is consistent after this call.
   */
  bool collectModelInfoHoTerm(Node n, TheoryModel* m);

 private:
  /** common constants */
  Node d_true;
  /** the parent of this extension */
  TheoryUF& d_parent;
  /** extensionality has been applied to these disequalities */
  NodeSet d_extensionality;

  /** cache of getExtensionalityDeq below */
  std::map<Node, Node> d_extensionality_deq;

  /** map from non-standard operators to their skolems */
  NodeNodeMap d_uf_std_skolem;
}; /* class TheoryUF */

}  // namespace uf
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__UF__HO_EXTENSION_H */
