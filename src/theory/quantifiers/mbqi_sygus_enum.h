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

class MVarInfo
{
 public:
  void initialize(const Node& v);
  Node getEnumeratedTerm(size_t i);
  bool isEnumerated() const;
 private:
   std::vector<Node> d_enum;
   std::vector<Node> d_lambdaVars;
  bool d_isEnum;
};

class MQuantInfo
{
public:
  void initialize(const Node& q);
  /** Get n^th instantiation from q for variable v */
  Node getEnumeratedTerm(size_t index, size_t i);
  /** Get indicies of variables to instantiate */
  std::vector<size_t> getIndicies();
private:
  Node d_quant;
  std::vector<MVarInfo> d_vinfo;
  std::vector<size_t> d_indices;
};

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
  MQuantInfo& getOrMkQuantInfo(const Node& q);
   std::map<Node, MQuantInfo> d_qinfo;
  InstStrategyMbqi& d_parent;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_MBQI_H */
