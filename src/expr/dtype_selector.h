/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a datatype selector.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__DTYPE_SELECTOR_H
#define CVC5__EXPR__DTYPE_SELECTOR_H

#include <string>
#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {

class DatatypeConstructorArg;
class DType;
class DTypeConstructor;

/**
 * A datatype selector for a constructor argument (i.e., a datatype field).
 */
class DTypeSelector
{
  friend class DatatypeConstructorArg;
  friend class DTypeConstructor;
  friend class DType;

 public:
  /** constructor */
  DTypeSelector(std::string name, Node selector, Node updater);

  /** Get the name of this constructor argument. */
  const std::string& getName() const;

  /**
   * Get the selector for this constructor argument; this call is
   * only permitted after resolution.
   */
  Node getSelector() const;
  /**
   * Get the upater for this constructor argument; this call is
   * only permitted after resolution.
   */
  Node getUpdater() const;

  /**
   * Get the associated constructor for this constructor argument;
   * this call is only permitted after resolution.
   */
  Node getConstructor() const;

  /**
   * Get the type of the selector for this constructor argument.
   */
  TypeNode getType() const;

  /**
   * Get the range type of this argument.
   */
  TypeNode getRangeType() const;

  /**
   * Returns true iff this constructor argument has been resolved.
   */
  bool isResolved() const;

  /** prints this datatype constructor argument to stream */
  void toStream(std::ostream& out) const;

 private:
  /** the name of this selector */
  std::string d_name;
  /** the selector expression */
  Node d_selector;
  /** the updater expression */
  Node d_updater;
  /**
   * The constructor associated with this selector. This field is initialized
   * by the constructor of this selector during a call to
   * DTypeConstructor::resolve.
   */
  Node d_constructor;
  /** whether this class has been resolved */
  bool d_resolved;
};

std::ostream& operator<<(std::ostream& os, const DTypeSelector& arg);

}  // namespace cvc5::internal

#endif
