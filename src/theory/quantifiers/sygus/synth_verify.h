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
 * Class for verifying a synthesis solution
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYNTH_VERIFY_H
#define CVC5__THEORY__QUANTIFIERS__SYNTH_VERIFY_H

#include <memory>

#include "options/options.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 * Class for verifying queries corresponding to synthesis conjectures
 */
class SynthVerify
{
 public:
  SynthVerify(TermDbSygus* tds);
  ~SynthVerify();
  /**
   * Verification call
   */
  Result verify(Node query, const std::vector<Node>& vars, std::vector<Node>& mvs);
 private:
  /** Pointer to the term database sygus */
  TermDbSygus* d_tds;
  /** The options for subsolver calls */
  Options d_subOptions;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
