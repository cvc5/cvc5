/*********************                                                        */
/*! \file relevance_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of relevance manager
 **/

#include "theory/relevance_manager.h"

namespace CVC4 {
namespace theory {

RelevanceManager::RelevanceManager(context::UserContext* userContext) : d_input(userContext){}
void RelevanceManager::computeRelevance();
bool RelevanceManager::isRelevant(Node lit);

}  // namespace theory
}  // namespace CVC4

