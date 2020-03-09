/*********************                                                        */
/*! \file idl_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include "context/cdhashmap.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * A reason for a value of a variable in the model is a constraint that implies
 * this value by means of the value of another variable. For example, if the
 * value of x is 0, then the variable x and the constraint (y > 0) are a reason
 * for the y taking the value 1.
 */
struct IDLReason
{
  /** The variable of the reason */
  TNode d_x;
  /** The constraint of the reason */
  TNode d_constraint;

  IDLReason(TNode x, TNode constraint) : d_x(x), d_constraint(constraint) {}
  IDLReason() {}
};

/**
 * A model maps variables to integer values and backs them up with reasons.
 * Default values (if not set with setValue) for all variables are 0.
 */
class IDLModel
{
  typedef context::CDHashMap<TNode, Integer, TNodeHashFunction> model_value_map;
  typedef context::CDHashMap<TNode, IDLReason, TNodeHashFunction>
      model_reason_map;

  /** Values assigned to individual variables */
  model_value_map d_model;

  /** Reasons constraining the individual variables */
  model_reason_map d_reason;

 public:
  IDLModel(context::Context* context);

  /** Get the model value of the variable */
  Integer getValue(TNode var) const;

  /** Set the value of the variable */
  void setValue(TNode var, Integer value, IDLReason reason);

  /** Get the cycle of reasons behind the variable var */
  void getReasonCycle(TNode var, std::vector<TNode>& reasons);

  /** Output to the given stream */
  void toStream(std::ostream& out) const;
};

inline std::ostream& operator<<(std::ostream& out, const IDLModel& model)
{
  model.toStream(out);
  return out;
}

}  // namespace idl
}  // namespace theory
}  // namespace CVC4
