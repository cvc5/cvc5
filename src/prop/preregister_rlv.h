/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preregister relevant formulas
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__PREREGISTER_RLV_H
#define CVC5__PROP__PREREGISTER_RLV_H

#include <iosfwd>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

/**
 */
class PreregisterRlv : protected EnvObj
{
  using NodeList = context::CDList<TNode>;

 public:
  PreregisterRlv(Env& env);

  ~PreregisterRlv();

  void notifyFormula(TNode n, std::vector<Node>& toPreregister);
  
  void notifyCheck(std::vector<Node>& toPreregister);
 private:
  /** Queue of asserted facts */
  NodeList d_preregistering;
  /** Index we have processed? */
  context::CDO<size_t> d_prindex;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PREREGISTER_RLV_H */
