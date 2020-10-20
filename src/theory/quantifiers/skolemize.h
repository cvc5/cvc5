/*********************                                                        */
/*! \file skolemize.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for skolemization
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SKOLEMIZE_H
#define CVC4__THEORY__QUANTIFIERS__SKOLEMIZE_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {

class DTypeConstructor;

namespace theory {
namespace quantifiers {

/** Skolemization utility
 *
 * This class constructs Skolemization lemmas.
 * Given a quantified formula q = (forall x. P),
 * its skolemization lemma is of the form:
 *   (~ forall x. P ) => ~P * { x -> d_skolem_constants[q] }
 *
 * This class also incorporates techniques for
 * skolemization with "inductive strenghtening", see
 * Section 2 of Reynolds et al., "Induction for SMT
 * Solvers", VMCAI 2015. In the case that x is an inductive
 * datatype or an integer, then we may strengthen the conclusion
 * based on weak well-founded induction. For example, for
 * quantification on lists, a skolemization with inductive
 * strengthening is a lemma of this form:
 *   (~ forall x : List. P( x ) ) =>
 *   ~P( k ) ^ ( is-cons( k ) => P( tail( k ) ) )
 * For the integers it is:
 *   (~ forall x : Int. P( x ) ) =>
 *   ~P( k ) ^ ( x>0 => P( x-1 ) )
 *
 *
 * Inductive strenghtening is not enabled by
 * default and can be enabled by option:
 *   --quant-ind
 */
class Skolemize
{
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

 public:
  Skolemize(QuantifiersEngine* qe, context::UserContext* u);
  ~Skolemize() {}
  /** skolemize quantified formula q
   * If the return value ret of this function
   * is non-null, then ret is a new skolemization lemma
   * we generated for q. These lemmas are constructed
   * once per user-context.
   */
  Node process(Node q);
  /** get skolem constants for quantified formula q */
  bool getSkolemConstants(Node q, std::vector<Node>& skolems);
  /** get the i^th skolem constant for quantified formula q */
  Node getSkolemConstant(Node q, unsigned i);
  /** make skolemized body
   *
   * This returns the skolemized body n of a
   * quantified formula q with inductive strenghtening,
   * where typically n is q[1].
   *
   * The skolem constants/functions we generate by this
   * skolemization are added to sk.
   *
   * The arguments fvTypes and fvs are used if we are
   * performing skolemization within a nested quantified
   * formula. In this case, skolem constants we introduce
   * must be parameterized based on fvTypes and must be
   * applied to fvs.
   *
   * The last two arguments sub and sub_vars are used for
   * to carry the body and indices of other induction
   * variables if a quantified formula to skolemize
   * has multiple induction variables. See page 5
   * of Reynolds et al., VMCAI 2015.
   */
  static Node mkSkolemizedBody(Node q,
                               Node n,
                               std::vector<TypeNode>& fvTypes,
                               std::vector<TNode>& fvs,
                               std::vector<Node>& sk,
                               Node& sub,
                               std::vector<unsigned>& sub_vars);
  /** get the skolemized body for quantified formula q */
  Node getSkolemizedBody(Node q);
  /** is n a variable that we can apply inductive strenghtening to? */
  static bool isInductionTerm(Node n);
  /** print all skolemizations
   * This is used for the command line option
   *   --dump-instantiations
   * which prints an informal justification
   * of steps taken by the quantifiers module.
   * Returns true if we printed at least one
   * skolemization.
   */
  bool printSkolemization(std::ostream& out);

 private:
  /** get self selectors
   * For datatype constructor dtc with type dt,
   * this collects the set of datatype selector applications,
   * applied to term n, whose return type in ntn, and stores
   * them in the vector selfSel.
   */
  static void getSelfSel(const DType& dt,
                         const DTypeConstructor& dc,
                         Node n,
                         TypeNode ntn,
                         std::vector<Node>& selfSel);
  /** quantifiers engine that owns this module */
  QuantifiersEngine* d_quantEngine;
  /** quantified formulas that have been skolemized */
  NodeNodeMap d_skolemized;
  /** map from quantified formulas to the list of skolem constants */
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction>
      d_skolem_constants;
  /** map from quantified formulas to their skolemized body */
  std::unordered_map<Node, Node, NodeHashFunction> d_skolem_body;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SKOLEMIZE_H */
