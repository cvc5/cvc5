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
 * Oracle caller
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__ORACLE_H
#define CVC5__EXPR__ORACLE_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * An oracle, which stores a function whose interface is from a vector of nodes
 * to a vector of nodes. It is expected to serve as an oracle interface as
 * described in Polgreen et al VMCAI 2022 and the SyGuS version 2.1 standard.
 */
class Oracle
{
 public:
  /** Construct an oracle whose implementation is the given function. */
  Oracle(std::function<std::vector<Node>(const std::vector<Node>&)> fn)
      : d_fn(fn)
  {
  }
  ~Oracle() {}
  /** Run the function on the given input */
  std::vector<Node> run(const std::vector<Node>& input) const
  {
    return d_fn(input);
  }
  /** Get the function for this oracle */
  std::function<std::vector<Node>(const std::vector<Node>&)> getFunction() const
  {
    return d_fn;
  }

 private:
  /** The function for this oracle */
  std::function<std::vector<Node>(const std::vector<Node>&)> d_fn;
};

}  // namespace cvc5::internal

#endif /*CVC5__EXPR__ORACLE_H*/
