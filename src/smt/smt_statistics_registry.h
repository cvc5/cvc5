/*********************                                                        */
/*! \file smt_statistics_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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


/**
 * To use a statistic, you need to declare it, initialize it in your
 * constructor, register it in your constructor, and deregister it in
 * your destructor.  Instead, this macro does it all for you (and
 * therefore also keeps the statistic type, field name, and output
 * string all in the same place in your class's header.  Its use is
 * like in this example, which takes the place of the declaration of a
 * statistics field "d_checkTimer":
 *
 *   KEEP_STATISTIC(TimerStat, d_checkTimer, "theory::uf::checkTime");
 *
 * If any args need to be passed to the constructor, you can specify
 * them after the string.
 *
 * The macro works by creating a nested class type, derived from the
 * statistic type you give it, which declares a registry-aware
 * constructor/destructor pair.
 */
#define KEEP_STATISTIC(_StatType, _StatField, _StatName, _CtorArgs...)  \
  struct Statistic_##_StatField : public _StatType {                    \
    Statistic_##_StatField() : _StatType(_StatName, ## _CtorArgs) {     \
      smtStatisticsRegistry()->registerStat(this);                 \
    }                                                                   \
    ~Statistic_##_StatField() {                                         \
      smtStatisticsRegistry()->unregisterStat(this);                         \
    }                                                                   \
  } _StatField


}/* CVC4 namespace */
