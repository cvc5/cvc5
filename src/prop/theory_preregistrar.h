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
 * Preregister policy
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__THEORY_PREREGISTRAR_H
#define CVC5__PROP__THEORY_PREREGISTRAR_H

#include <iosfwd>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "decision/prop_finder.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

/**
 */
class TheoryPreregistrar : protected EnvObj
{
  using NodeList = context::CDList<TNode>;

 public:
  TheoryPreregistrar(Env& env, TheoryEngine* te);

  ~TheoryPreregistrar();

  /** Do we need to be informed of activated skolem definitions? */
  bool needsActiveSkolemDefs() const;
  /** Notify assertion */
  void addAssertion(TNode n, TNode skolem, bool isLemma);
  void notifyActiveSkolemDefs(std::vector<TNode>& defs);
  /** Notify that n is preregistered by SAT solver */
  void notifyPreRegister(TNode n);
  /** Notify that n is asserted from SAT solver */
  void notifyAsserted(TNode n);

 private:
  /** pre-register to theory */
  void preRegisterToTheory(const std::vector<Node>& toPreregister);
  /** Theory engine */
  TheoryEngine* d_theoryEngine;
  /** Propagation finder */
  std::unique_ptr<decision::PropFinder> d_propFinder;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__PREREGISTER_RLV_H */
