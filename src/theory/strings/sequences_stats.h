/*********************                                                        */
/*! \file sequences_stats.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__SEQUENCES_STATS_H
#define CVC4__THEORY__STRINGS__SEQUENCES_STATS_H

#include "theory/strings/infer_info.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace strings {

class SequencesStatistics
{
 public:
  SequencesStatistics();
  ~SequencesStatistics();

  /** Counts the number of inferences made of each type of inference */
  HistogramStat<Inference> d_inferences;
};


}
}
}

#endif /* CVC4__THEORY__STRINGS__SEQUENCES_STATS_H */
