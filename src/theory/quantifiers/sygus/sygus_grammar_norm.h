/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for simplifying SyGuS grammars after they are encoded into datatypes.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H

#include <map>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class SygusGrammarNorm;
class TermDbSygus;

/**
 * Utility for normalizing SyGuS grammars to avoid spurious enumerations
 */
class SygusGrammarNorm : protected EnvObj
{
 public:
  SygusGrammarNorm(Env& env);
  ~SygusGrammarNorm() {}
  /** creates a normalized typenode from a given one.
   *
   * In a normalized typenode all typenodes it contains are normalized.
   * Normalized typenodes can be structurally identicial to their original
   * counterparts.
   *
   * sygus_vars are the input variables for the function to be synthesized,
   * which are used as input for the built datatypes.
   *
   * This is the function that will resolve all types and datatypes built during
   * normalization. This operation can only be performed after all types
   * contained in "tn" have been normalized, since the resolution of datatypes
   * depends on all types involved being defined.
   *
   * @param tn The sygus datatype to normalize.
   * @param sygusVars A bound variable list indicating the formal argument list
   * of a function-to-synthesize for the grammar.
   * @return A sygus datatype corresponding to the normalization of tn.
   */
  TypeNode normalizeSygusType(TypeNode tn, Node sygusVars);
  /**
   * Same as above, but with a sygus grammar.
   *
   * @param g The sygus grammar to normalize.
   * @return A sygus datatype corresponding to resolving the normalization of g.
   */
  TypeNode normalizeSygusType(Grammar g);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
