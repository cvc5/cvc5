/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for the development of a Listener interface class.
 *
 * This class provides a single notification that must be overwritten.
 */

#include "cvc5_public.h"

#ifndef CVC5__LISTENER_H
#define CVC5__LISTENER_H

namespace cvc5::internal {

/**
 * Listener interface class.
 *
 * The interface provides a notify() function.
 */
class Listener
{
 public:
  Listener();
  virtual ~Listener();

  /** Note that notify may throw arbitrary exceptions. */
  virtual void notify() = 0;
};

}  // namespace cvc5::internal

#endif /* CVC5__LISTENER_H */
