/*********************                                                        */
/*! \file ee_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for management of equality engines.
 **/

#include "theory/ee_manager.h"

namespace CVC4 {
namespace theory {

const EeTheoryInfo* EqEngineManager::getEeTheoryInfo(TheoryId tid) const
{
  std::map<TheoryId, EeTheoryInfo>::const_iterator it = d_einfo.find(tid);
  if (it != d_einfo.end())
  {
    return &it->second;
  }
  return nullptr;
}

}  // namespace theory
}  // namespace CVC4
