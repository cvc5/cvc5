/*********************                                                        */
/*! \file portfolio.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Provides (somewhat) generic functionality to simulate a
 ** (potentially cooperative) race
 **/

#include <boost/function.hpp>
#include <boost/thread.hpp>
#include <boost/bind.hpp>
#include <boost/thread/condition.hpp>
#include <boost/exception_ptr.hpp>

#include "base/output.h"
#include "options/options.h"
#include "smt/smt_engine.h"
#include "util/result.h"
#include "util/statistics_registry.h"

namespace CVC4 {

/** Mutex to make sure at most one thread is winner */
boost::mutex mutex_done;

/** Mutex / condition variable to notify main when winner data written */
boost::mutex mutex_main_wait;
boost::condition_variable condition_var_main_wait;

bool global_flag_done;
int global_winner;

template<typename S>
void runThread(int thread_id, boost::function<S()> threadFn, S& returnValue)
{
  /* Uncomment line to delay first thread, useful to unearth errors/debug */
  // if(thread_id == 0) { sleep(1); }
  returnValue = threadFn();

  if( mutex_done.try_lock() ) {
    if(global_flag_done == false) 
    {
      {
        boost::lock_guard<boost::mutex> lock(mutex_main_wait);
        global_winner = thread_id;
        global_flag_done = true;
      }
      condition_var_main_wait.notify_all(); // we want main thread to quit
    }
    mutex_done.unlock();
  }
}

template<typename T, typename S>
std::pair<int, S> runPortfolio(int numThreads,
                               boost::function<T()> driverFn,
                               boost::function<S()> threadFns[],
                               size_t stackSize,
                               bool optionWaitToJoin,
                               TimerStat& statWaitTime) {
  boost::thread thread_driver;
  boost::thread* threads = new boost::thread[numThreads];
  S* threads_returnValue = new S[numThreads];

  global_flag_done = false;
  global_winner = -1;

  for(int t = 0; t < numThreads; ++t) {

#if BOOST_HAS_THREAD_ATTR
    boost::thread::attributes attrs;

    if(stackSize > 0) {
      attrs.set_stack_size(stackSize);
    }

    threads[t] =
      boost::thread(attrs, boost::bind(runThread<S>, t, threadFns[t],
                                       boost::ref(threads_returnValue[t]) ) );
#else /* BOOST_HAS_THREAD_ATTR */
    if(stackSize > 0) {
      throw OptionException("cannot specify a stack size for worker threads; requires CVC4 to be built with Boost thread library >= 1.50.0");
    }

    threads[t] =
      boost::thread(boost::bind(runThread<S>, t, threadFns[t],
                                boost::ref(threads_returnValue[t]) ) );

#endif /* BOOST_HAS_THREAD_ATTR */

#if defined(BOOST_THREAD_PLATFORM_PTHREAD)
    if(Chat.isOn()) {
      void *stackaddr;
      size_t stacksize;
      pthread_attr_t attr;
      pthread_getattr_np(threads[t].native_handle(), &attr);
      pthread_attr_getstack(&attr, &stackaddr, &stacksize);
      Chat() << "Created worker thread " << t << " with stack size " << stacksize << std::endl;
    }
#endif
  }

  if(not driverFn.empty())
    thread_driver = boost::thread(driverFn);

  boost::unique_lock<boost::mutex> lock(mutex_main_wait);
  while(global_flag_done == false) {
    condition_var_main_wait.wait(lock);
  }

  statWaitTime.start();

  if(not driverFn.empty()) {
    thread_driver.interrupt();
    thread_driver.join();
  }

  for(int t = 0; t < numThreads; ++t) {
    if(optionWaitToJoin) {
      threads[t].join();
    }
  }

  std::pair<int, S> retval(global_winner, threads_returnValue[global_winner]);

  delete[] threads;
  delete[] threads_returnValue;

  return retval;
}

// instantiation
template
std::pair<int, bool>
runPortfolio<void, bool>(int,
                         boost::function<void()>, 
                         boost::function<bool()>*,
                         size_t,
                         bool,
                         TimerStat&);

}/* CVC4 namespace */
