/*********************                                                        */
/*! \file portfolio.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <boost/function.hpp>
#include <boost/thread.hpp>
#include <boost/bind.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>

#include "smt/smt_engine.h"
#include "util/result.h"
#include "util/options.h"

using namespace boost;

namespace CVC4 {

mutex mutex_done;
mutex mutex_main_wait;
condition condition_var_main_wait;

bool global_flag_done = false;
int global_winner = -1;

template<typename S>
void runThread(int thread_id, function<S()> threadFn, S& returnValue) {
  returnValue = threadFn();

  if( mutex_done.try_lock() ) {
    if(global_flag_done == false) {
      global_flag_done = true;
      global_winner = thread_id;
    }
    mutex_done.unlock();
    condition_var_main_wait.notify_all(); // we want main thread to quit
  }
}

template<typename T, typename S>
std::pair<int, S> runPortfolio(int numThreads,
                               function<T()> driverFn,
                               function<S()> threadFns[],
                               bool optionWaitToJoin) {
  thread thread_driver;
  thread threads[numThreads];
  S threads_returnValue[numThreads];

  for(int t = 0; t < numThreads; ++t) {
    threads[t] = thread(bind(runThread<S>, t, threadFns[t], ref(threads_returnValue[t]) ));
  }

  if(not driverFn.empty())
    thread_driver = boost::thread(driverFn);

  while(global_flag_done == false)
    condition_var_main_wait.wait(mutex_main_wait);

  if(not driverFn.empty()) {
    thread_driver.interrupt();
    thread_driver.join();
  }

  for(int t = 0; t < numThreads; ++t) {
    if(optionWaitToJoin) {
      threads[t].join();
    }
  }

  return std::pair<int, S>(global_winner,threads_returnValue[global_winner]);
}

// instantiation
template
std::pair<int, Result>
runPortfolio<void, Result>(int, boost::function<void()>, boost::function<Result()>*, bool);

}/* CVC4 namespace */
