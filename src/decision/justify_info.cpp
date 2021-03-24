/*********************                                                        */
/*! \file justify_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification info
 **/

#include "decision/justify_info.h"

namespace CVC4 {

JustifyInfo::JustifyInfo(context::Context* c)
    : d_node(c), d_desiredVal(c, prop::SAT_VALUE_UNKNOWN), d_childIndex(c, 0)
{
}

}  // namespace CVC4
