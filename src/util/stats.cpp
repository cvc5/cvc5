/*********************                                                        */
/*! \file stats.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/stats.h"

using namespace CVC4;

StatisticsRegistry::StatSet StatisticsRegistry::d_registeredStats;

std::string Stat::s_delim(",");




void StatisticsRegistry::flushStatistics(std::ostream& out){
#ifdef CVC4_STATISTICS_ON
  for(StatSet::iterator i=d_registeredStats.begin();i != d_registeredStats.end();++i){
    Stat* s = *i;
    s->flushStat(out);
    out << std::endl;
  }
#endif
}
