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
 * List of instantiations.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H
#define CVC5__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace cvc5 {

/** A list of instantiations for a quantified formula */
struct InstantiationList
{
  InstantiationList(Node q, const std::vector<std::vector<Node> >& inst)
      : d_quant(q), d_inst(inst)
  {
  }
  /** The quantified formula */
  Node d_quant;
  /** The instantiation list */
  std::vector<std::vector<Node> > d_inst;
};

/** Print the instantiation list to stream out */
std::ostream& operator<<(std::ostream& out, const InstantiationList& ilist);

/** The list of skolemization for a quantified formula */
struct SkolemList
{
  SkolemList(Node q, const std::vector<Node>& sks) : d_quant(q), d_sks(sks) {}
  /** The quantified formula */
  Node d_quant;
  /** The list of skolems for the quantified formula */
  std::vector<Node> d_sks;
};

/** Print the skolem list to stream out */
std::ostream& operator<<(std::ostream& out, const SkolemList& skl);

}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H */
