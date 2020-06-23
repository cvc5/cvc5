/*********************                                                        */
/*! \file smt_statistics_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Accessor for the SmtEngine's StatisticsRegistry.
 **
 ** Accessor for the SmtEngine's StatisticsRegistry.
 **/

#include "cvc4_private.h"

#pragma once

#include "util/statistics_registry.h"

namespace CVC4 {

/**
 * This returns the StatisticsRegistry attached to the currently in scope
 * SmtEngine. This is a synonym for smt::SmtScope::currentStatisticsRegistry().
 */
StatisticsRegistry* smtStatisticsRegistry();

}/* CVC4 namespace */
