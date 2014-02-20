/*********************                                                        */
/*! \file portfolio.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Provides (somewhat) generic functionality to simulate a
 ** (potentially cooperative) race
 **/

#ifndef __CVC4__PORTFOLIO_H
#define __CVC4__PORTFOLIO_H

#include <boost/function.hpp>
#include <utility>

#include "smt/smt_engine.h"
#include "expr/command.h"
#include "options/options.h"
#include "util/statistics_registry.h"

namespace CVC4 {

template<typename T, typename S>
std::pair<int, S> runPortfolio(int numThreads, 
                               boost::function<T()> driverFn,
                               boost::function<S()> threadFns[],
                               bool optionWaitToJoin,
                               TimerStat& statWaitTime);
// as we have defined things, S=void would give compile errors
// do we want to fix this? yes, no, maybe?

}/* CVC4 namespace */

#endif /* __CVC4__PORTFOLIO_H */
