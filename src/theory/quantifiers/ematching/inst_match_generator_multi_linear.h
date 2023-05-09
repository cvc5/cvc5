/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Multi-linear inst match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_MULTI_LINEAR_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_MULTI_LINEAR_H

#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** InstMatchGeneratorMultiLinear class
 *
 * This is the default implementation of multi-triggers.
 *
 * Handling multi-triggers using this class is done by constructing a linked
 * list of InstMatchGenerator classes (see mkInstMatchGeneratorMulti), with one
 * InstMatchGeneratorMultiLinear at the head and a list of trailing
 * InstMatchGenerators.
 *
 * cvc5 employs techniques that ensure that the number of instantiations
 * is worst-case polynomial wrt the number of ground terms, where this class
 * lifts this policy to multi-triggers. In particular consider
 *
 *  multi-trigger : { f( x1 ), f( x2 ), f( x3 ), f( x4 ) }
 *
 * For this multi-trigger, we insist that for each i=1...4, and each ground term
 * t, there is at most 1 instantiation added as a result of matching
 *    ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) )
 * against ground terms of the form
 *    ( s_1, s_2, s_3, s_4 ) where t = s_i for i=1,...,4.
 * Meaning we add instantiations for the multi-trigger
 * ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ) based on matching pairwise against:
 *   ( f( c_i11 ), f( c_i21 ), f( c_i31 ), f( c_i41 ) )
 *   ( f( c_i12 ), f( c_i22 ), f( c_i32 ), f( c_i42 ) )
 *   ( f( c_i13 ), f( c_i23 ), f( c_i33 ), f( c_i43 ) )
 * Where we require c_i{jk} != c_i{jl} for each i=1...4, k != l.
 *
 * For example, we disallow adding instantiations based on matching against both
 * ( f( c_1 ), f( c_2 ), f( c_4 ), f( c_6 ) ) and
 * ( f( c_1 ), f( c_3 ), f( c_5 ), f( c_7 ) )
 * against ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ), since f( c_1 ) is matched
 * against f( x1 ) twice.
 *
 * This policy can be disabled by --no-multi-trigger-linear.
 *
 */
class InstMatchGeneratorMultiLinear : public InstMatchGenerator
{
  friend class InstMatchGenerator;

 public:
  /** Reset. */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(InstMatch& m) override;

 protected:
  /** reset the children of this generator */
  int resetChildren();
  /** constructor */
  InstMatchGeneratorMultiLinear(Env& env,
                                Trigger* tparent,
                                Node q,
                                std::vector<Node>& pats);
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
