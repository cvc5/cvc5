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
 * Implementation of LFSC node conversion for list variables in side conditions
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_LIST_SC_NODE_CONVERTER_H
#define CVC4__PROOF__LFSC__LFSC_LIST_SC_NODE_CONVERTER_H

#include "expr/node_converter.h"
#include "proof/lfsc/lfsc_node_converter.h"

namespace cvc5 {
namespace proof {

/** Convert list variables in side conditions */
class LfscListScNodeConverter : public NodeConverter
{
 public:
  LfscListScNodeConverter(LfscNodeConverter& conv);
  /** convert to internal */
  Node postConvert(Node n) override;

 private:
  /** The parent converter, used for getting internal symbols and utilities */
  LfscNodeConverter& d_conv;
};

}  // namespace proof
}  // namespace cvc5

#endif
