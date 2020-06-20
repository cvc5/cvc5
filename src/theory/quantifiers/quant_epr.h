/*********************                                                        */
/*! \file quant_epr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier util
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANT_EPR_H
#define CVC4__THEORY__QUANT_EPR_H

#include <map>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Quant EPR
 *
 * This class maintains information required for
 * approaches for effectively propositional logic (EPR),
 * also called the Bernays-Schoenfinkel fragment.
 *
 * It maintains for each type whether the type
 * has a finite Herbrand universe, stored in d_consts.
 * This class is used in counterexample-guided instantiation
 * for EPR, described in Reynolds et al.,
 * "Reasoning in the Bernays-Schonfinkel-Ramsey Fragment of
 * Separation Logic", VMCAI 2017.
 *
 * Below, we say a type is an "EPR type" if its
 * Herbrand universe can be restricted to a finite set
 * based on the set of input assertions,
 * and a "non-EPR type" otherwise.
 */
class QuantEPR
{
 public:
  QuantEPR() {}
  virtual ~QuantEPR() {}
  /** constants per type */
  std::map<TypeNode, std::vector<Node> > d_consts;
  /** register an input assertion with this class
   * This updates whether types are EPR are not
   * based on the constraints in assertion.
   */
  void registerAssertion(Node assertion);
  /** finish initialize
   * This ensures all EPR sorts are non-empty
   * (that is, they have at least one term in d_consts),
   * and clears non-EPR sorts from d_consts.
   */
  void finishInit();
  /** is type tn an EPR type? */
  bool isEPR(TypeNode tn) const
  {
    return d_non_epr.find(tn) == d_non_epr.end();
  }
  /** is k an EPR constant for type tn? */
  bool isEPRConstant(TypeNode tn, Node k);
  /** add EPR constant k of type tn. */
  void addEPRConstant(TypeNode tn, Node k);
  /** get EPR axiom for type
   * This is a formula of the form:
   *   forall x : U. ( x = c1 V ... x = cn )
   * where c1...cn are the constants in the Herbrand
   * universe of U.
   */
  Node mkEPRAxiom(TypeNode tn);
  /** does this class have an EPR axiom for type tn? */
  bool hasEPRAxiom(TypeNode tn) const
  {
    return d_epr_axiom.find(tn) != d_epr_axiom.end();
  }

 private:
  /** register the node */
  void registerNode(Node n,
                    std::map<int, std::map<Node, bool> >& visited,
                    bool beneathQuant,
                    bool hasPol,
                    bool pol);
  /** map from types to a flag says whether they are not EPR */
  std::map<TypeNode, bool> d_non_epr;
  /** EPR axioms for each type. */
  std::map<TypeNode, Node> d_epr_axiom;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANT_EPR_H */
