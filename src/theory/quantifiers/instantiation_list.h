/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/inference_id.h"

namespace cvc5::internal {

struct InstantiationVec
{
 public:
  InstantiationVec(const std::vector<Node>& vec,
                   theory::InferenceId id = theory::InferenceId::UNKNOWN,
                   Node pfArg = Node::null());
  /** The vector of terms */
  std::vector<Node> d_vec;
  /** The inference id */
  theory::InferenceId d_id;
  /** The proof argument */
  Node d_pfArg;
};

/** A list of instantiations for a quantified formula */
struct InstantiationList
{
  /** Initialize */
  void initialize(Node q);
  /** The quantified formula */
  Node d_quant;
  /** The instantiation list */
  std::vector<InstantiationVec> d_inst;
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

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INSTANTIATION_LIST_H */
