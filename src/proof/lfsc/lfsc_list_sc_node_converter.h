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

/**
 * Convert list variables in side conditions
 *
 * This runs in two modes.
 * - If isPre is true, then the input is in its original form, and we add
 * applications of nary_elim.
 * - If isPre is false, then the input is in converted form, and we add
 * applications of nary_concat.
 */
class LfscListScNodeConverter : public NodeConverter
{
 public:
  LfscListScNodeConverter(LfscNodeConverter& conv,
                          const std::unordered_set<Node>& listVars,
                          bool isPre = false);
  /** convert to internal */
  Node postConvert(Node n) override;

 private:
  /** Make application for */
  Node mkOperatorFor(const std::string& name,
                     const std::vector<Node>& children,
                     TypeNode retType);
  /** The parent converter, used for getting internal symbols and utilities */
  LfscNodeConverter& d_conv;
  /** Variables we are treating as list variables */
  std::unordered_set<Node> d_listVars;
  /** In pre or post */
  bool d_isPre;
};

}  // namespace proof
}  // namespace cvc5

#endif
