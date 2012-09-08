/*********************                                                        */
/*! \file portfolio.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

namespace CVC4 {

template<typename T, typename S>
std::pair<int, S> runPortfolio(int numThreads, 
                              boost::function<T()> driverFn,
                              boost::function<S()> threadFns[],
                              bool optionWaitToJoin);
// as we have defined things, S=void would give compile errors
// do we want to fix this? yes, no, maybe?

}/* CVC4 namespace */

#endif /* __CVC4__PORTFOLIO_H */
