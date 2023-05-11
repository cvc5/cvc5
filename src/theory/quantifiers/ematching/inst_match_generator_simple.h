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
 * Simple inst match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_SIMPLE_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_SIMPLE_H

#include <map>
#include <vector>

#include "expr/node_trie.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** InstMatchGeneratorSimple class
 *
 * This is the default generator class for simple single triggers.
 * For example, { f( x, a ) }, { f( x, x ) } and { f( x, y ) } are simple single
 * triggers. In practice, around 70-90% of triggers are simple single triggers.
 *
 * Notice that simple triggers also can have an attached polarity.
 * For example, { P( x ) = false }, { f( x, y ) = a } and { ~f( a, x ) = b } are
 * simple single triggers.
 *
 * The implementation traverses the term indices in TermDatabase for adding
 * instantiations, which is more efficient than the techniques required for
 * handling non-simple single triggers.
 */
class InstMatchGeneratorSimple : public IMGenerator
{
 public:
  /** constructors */
  InstMatchGeneratorSimple(Env& env, Trigger* tparent, Node q, Node pat);

  /** Reset instantiation round. */
  void resetInstantiationRound() override;
  /** Add instantiations. */
  uint64_t addInstantiations(InstMatch& m) override;
  /** Get active score. */
  int getActiveScore() override;

 private:
  /** quantified formula for the trigger term */
  Node d_quant;
  /** the trigger term */
  Node d_match_pattern;
  /** equivalence class polarity information
   *
   * This stores the required polarity/equivalence class with this trigger.
   * If d_eqc is non-null, we only produce matches { x->t } such that
   * our context does not entail
   *   ( d_match_pattern*{ x->t } = d_eqc) if d_pol = true, or
   *   ( d_match_pattern*{ x->t } != d_eqc) if d_pol = false.
   * where * denotes application of substitution.
   */
  bool d_pol;
  Node d_eqc;
  /** Match pattern arg types.
   * Cached values of d_match_pattern[i].getType().
   */
  std::vector<TypeNode> d_match_pattern_arg_types;
  /** The match operator d_match_pattern (see TermDb::getMatchOperator). */
  Node d_op;
  /**
   * Map from child number of d_match_pattern to variable index, or -1 if the
   * child is not a variable.
   */
  std::map<size_t, int> d_var_num;
  /** add instantiations, helper function.
   *
   * @param m the current match we are building,
   * @param addedLemmas the number of lemmas we have added via calls to
   * Instantiate::addInstantiation(...),
   * @param argIndex the argument index in d_match_pattern we are currently
   * matching,
   * @param tat the term index we are currently traversing.
   */
  void addInstantiations(InstMatch& m,
                         uint64_t& addedLemmas,
                         size_t argIndex,
                         TNodeTrie* tat);
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
