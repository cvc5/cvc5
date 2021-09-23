/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Basic sygus enumerator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BASIC_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BASIC_H

#include <map>
#include <unordered_set>
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers/sygus/enum_val_generator.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/type_enumerator.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/** A basic sygus value generator
 *
 * This class is a "naive" term generator for sygus conjectures, which invokes
 * the type enumerator to generate a stream of (all) sygus terms of a given
 * type.
 */
class EnumValGeneratorBasic : public EnumValGenerator
{
 public:
  EnumValGeneratorBasic(TermDbSygus* tds, TypeNode tn);
  ~EnumValGeneratorBasic() {}
  /** initialize (do nothing) */
  void initialize(Node e) override {}
  /** initialize (do nothing) */
  void addValue(Node v) override { d_currTerm = *d_te; }
  /**
   * Get next returns the next (T-rewriter-unique) value based on the type
   * enumerator.
   */
  bool increment() override;
  /** get the current term */
  Node getCurrent() override { return d_currTerm; }

 private:
  /** pointer to term database sygus */
  TermDbSygus* d_tds;
  /** the type enumerator */
  TypeEnumerator d_te;
  /** the current term */
  Node d_currTerm;
  /** cache of (enumerated) builtin values we have enumerated so far */
  std::unordered_set<Node> d_cache;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BASIC_H */
