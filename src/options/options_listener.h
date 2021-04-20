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
 * Base class for option listener.
 */

#include "cvc5_private.h"

#ifndef CVC5__OPTIONS__OPTIONS_LISTENER_H
#define CVC5__OPTIONS__OPTIONS_LISTENER_H

#include <string>

namespace cvc5 {

class OptionsListener
{
 public:
  OptionsListener() {}
  virtual ~OptionsListener() {}
  /**
   * Notify that option key has been set.
   */
  virtual void notifySetOption(const std::string& key) = 0;
};

}  // namespace cvc5

#endif /* CVC5__OPTIONS__OPTION_LISTENER_H */
