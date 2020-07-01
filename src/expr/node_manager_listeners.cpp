/*********************                                                        */
/*! \file node_manager_listeners.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Listeners that NodeManager registers to its Options object.
 **
 ** Listeners that NodeManager registers to its Options object.
 **/

#include "node_manager_listeners.h"

#include "base/listener.h"
#include "options/smt_options.h"
#include "util/resource_manager.h"

namespace CVC4 {
namespace expr {


void TlimitListener::notify() {
  d_rm->setTimeLimit(options::cumulativeMillisecondLimit(), true);
}

void TlimitPerListener::notify() {
  d_rm->setTimeLimit(options::perCallMillisecondLimit(), false);
}

void RlimitListener::notify() {
  d_rm->setTimeLimit(options::cumulativeResourceLimit(), true);
}

void RlimitPerListener::notify() {
  d_rm->setTimeLimit(options::perCallResourceLimit(), false);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */
