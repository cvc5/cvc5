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

#include "expr/sygus_term_enumerator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class InstStrategyMbqi;

class MVarInfo
{
 public:
  void initialize(Env& env, const Node& q, const Node& v, const std::vector<Node>& etrules);
  Node getEnumeratedTerm(size_t i);

 private:
  std::unique_ptr<SygusTermEnumerator> d_senum;
  std::vector<Node> d_enum;
  Node d_lamVars;
};

class MQuantInfo
{
 public:
  void initialize(Env& env, const Node& q);
  /** Get indicies of variables to instantiate */
  std::vector<size_t> getInstIndicies();
  /** Get indicies of variables not to instantiate */
  std::vector<size_t> getNoInstIndicies();
  /** Get variable info */
  MVarInfo& getVarInfo(size_t index);
  /** Should we enumerate terms for type tn? */
  static bool shouldEnumerate(const TypeNode& tn);
 private:
  Node d_quant;
  std::vector<MVarInfo> d_vinfo;
  std::vector<size_t> d_indices;
  std::vector<size_t> d_nindices;
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
   * Returns true if successful.
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
