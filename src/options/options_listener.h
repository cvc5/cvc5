/*********************                                                        */
/*! \file options_listener.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base class for option listener
 **/

#include "cvc4_private.h"

#ifndef CVC4__OPTIONS__OPTIONS_LISTENER_H
#define CVC4__OPTIONS__OPTIONS_LISTENER_H

#include <string>

namespace CVC4 {

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

}  // namespace CVC4

#endif /* CVC4__OPTIONS__OPTION_LISTENER_H */
