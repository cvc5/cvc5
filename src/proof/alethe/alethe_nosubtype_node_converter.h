/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alethe node conversion to remove subtyping
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALETHE__ALETHE_NOSUBTYPE_NODE_CONVERTER_H
#define CVC4__PROOF__ALETHE__ALETHE_NOSUBTYPE_NODE_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5 {
namespace proof {

/**
 * This is a helper class for the Alethe post-processor that converts nodes into
 * form that Alethe expects. In particular it removes occurrences of mixed
 * int/real typing.
 */
class AletheNoSubtypeNodeConverter : public NodeConverter
{
 public:
  AletheNoSubtypeNodeConverter() {}
  ~AletheNoSubtypeNodeConverter() {}
  /** Convert by casting integer terms into real ones when it's identified that
   * they occur in "real" positions. For example, (f 1 a), with f having as its
   * type f : Real -> Real -> Real, will be turned into (f 1.0 a). */
  Node postConvert(Node n) override;
};

}  // namespace proof
}  // namespace cvc5

#endif
