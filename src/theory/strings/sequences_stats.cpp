/*********************                                                        */
/*! \file sequences_stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for the theory of strings/sequences
 **/


#include "theory/strings/sequences_stats.h"

#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace strings {

SequencesStatistics::SequencesStatistics()
    : d_inferences("theory::strings::inferences")
{
  smtStatisticsRegistry()->registerStat(&d_inferences);
}

SequencesStatistics::~SequencesStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_inferences);
}

}
}
}
