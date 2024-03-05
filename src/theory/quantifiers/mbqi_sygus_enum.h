/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model-based quantifier instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MBQI_SYGUS_ENUM_H
#define CVC5__THEORY__QUANTIFIERS__MBQI_SYGUS_ENUM_H

#include <map>
#include <unordered_map>

#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class InstStrategyMbqi;

/**
 * MbqiSygusEnum
 */
class MbqiSygusEnum : protected EnvObj
{
 public:
  MbqiSygusEnum(Env& env, InstStrategyMbqi& parent);
  ~MbqiSygusEnum() {}

  /**
   * Updates mvs to the desired instantiation of q.
   */
  bool constructInstantiation(const Node& q,
                              const Node& query,
                              const std::vector<Node>& vars,
                              std::vector<Node>& mvs);

 private:
  InstStrategyMbqi& d_parent;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_MBQI_H */
