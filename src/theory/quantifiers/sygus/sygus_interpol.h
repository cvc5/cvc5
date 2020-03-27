/*********************                                                        */
/*! \file sygus_interpol.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus interpolation utility, which transforms an arbitrary input into
 *an
 ** interpolation problem.
 **/

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H

#include <string>
#include <vector>

#include "expr/node.h"
#include "expr/type.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusInterpol
 *
 * A utility that turns a set of quantifier-free assertions into
 * a sygus conjecture that encodes an interpolation problem. In detail, if our
 * input formula is F( x ) for free symbols x, and is partitioned into axioms Fa
 * and conjecture Fc then the sygus conjecture we construct is:
 *
 * exists A. forall x. ( (Fa( x ) => A( x )) ^ (A( x ) => Fc( x )) )
 *
 * where A( x ) is a predicate over the free symbols of our input that are
 * shared between Fa and Fc. In other words, A( x ) must be implied by our
 * axioms Fa and imply Fc( x ). We encode this conjecture using
 * SygusSideConditionAttribute.
 */
class SygusInterpol
{
 public:
  SygusInterpol();

  /**
   * Returns the sygus conjecture corresponding to the interpolation problem for
   * input problem (F above) given by axioms (Fa above), and conj (Fc above).
   * Note that axioms is expected to be a subset of asserts.
   *
   * The argument name is the name for the interpol-to-synthesize.
   *
   * The relationship between the free variables of asserts and the formal
   * argument list of the interpol-to-synthesize are tracked by the attribute
   * SygusVarToTermAttribute.
   *
   * In particular, solutions to the synthesis conjecture will be in the form
   * of a closed term (lambda varlist. t). The intended solution, which is a
   * term whose free variables are a subset of asserts, is the term
   * t * { varlist -> SygusVarToTermAttribute(varlist) }.
   */
  static Node mkInterpolationConjecture(const std::string& name,
                                    const std::vector<Node>& axioms,
                                    const Node& conj);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H */
