/*********************                                                        */
/*! \file portfolio_util.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Code relevant only for portfolio builds
 **/

#ifndef __CVC4__PORTFOLIO_UTIL_H
#define __CVC4__PORTFOLIO_UTIL_H

#include <queue>

#include "expr/pickler.h"
#include "util/channel.h"
#include "util/lemma_input_channel.h"
#include "util/lemma_output_channel.h"
#include "util/output.h"
#include "main/options.h"

namespace CVC4 {

typedef expr::pickle::Pickle ChannelFormat;

class PortfolioLemmaOutputChannel : public LemmaOutputChannel {
private:
  std::string d_tag;
  SharedChannel<ChannelFormat>* d_sharedChannel;
  expr::pickle::MapPickler d_pickler;

public:
  int cnt;
  PortfolioLemmaOutputChannel(std::string tag,
                              SharedChannel<ChannelFormat> *c,
                              ExprManager* em,
                              VarMap& to,
                              VarMap& from) :
    d_tag(tag),
    d_sharedChannel(c),
    d_pickler(em, to, from),
    cnt(0)
  {}

  ~PortfolioLemmaOutputChannel() throw() { }

  void notifyNewLemma(Expr lemma) {
    if(int(lemma.getNumChildren()) > options::sharingFilterByLength()) {
      return;
    }
    ++cnt;
    Trace("sharing") << d_tag << ": " << lemma << std::endl;
    expr::pickle::Pickle pkl;
    try {
      d_pickler.toPickle(lemma, pkl);
      d_sharedChannel->push(pkl);
      if(Trace.isOn("showSharing") && options::thread_id() == 0) {
        *options::out() << "thread #0: notifyNewLemma: " << lemma
                        << std::endl;
      }
    } catch(expr::pickle::PicklingException& p){
      Trace("sharing::blocked") << lemma << std::endl;
    }
  }

};/* class PortfolioLemmaOutputChannel */

class PortfolioLemmaInputChannel : public LemmaInputChannel {
private:
  std::string d_tag;
  SharedChannel<ChannelFormat>* d_sharedChannel;
  expr::pickle::MapPickler d_pickler;

public:
  PortfolioLemmaInputChannel(std::string tag,
                             SharedChannel<ChannelFormat>* c,
                             ExprManager* em,
                             VarMap& to,
                             VarMap& from) :
    d_tag(tag),
    d_sharedChannel(c),
    d_pickler(em, to, from){
  }

  ~PortfolioLemmaInputChannel() throw() { }

  bool hasNewLemma(){
    Debug("lemmaInputChannel") << d_tag << ": " << "hasNewLemma" << std::endl;
    return !d_sharedChannel->empty();
  }

  Expr getNewLemma() {
    Debug("lemmaInputChannel") << d_tag << ": " << "getNewLemma" << std::endl;
    expr::pickle::Pickle pkl = d_sharedChannel->pop();

    Expr e = d_pickler.fromPickle(pkl);
    if(Trace.isOn("showSharing") && options::thread_id() == 0) {
      *options::out() << "thread #0: getNewLemma: " << e << std::endl;
    }
    return e;
  }

};/* class PortfolioLemmaInputChannel */

std::vector<Options> parseThreadSpecificOptions(Options opts);

template<typename T>
void sharingManager(unsigned numThreads,
                    SharedChannel<T> *channelsOut[], // out and in with respect
                    SharedChannel<T> *channelsIn[],
                    SmtEngine *smts[])  // to smt engines
{
  Trace("sharing") << "sharing: thread started " << std::endl;
  std::vector <int> cnt(numThreads); // Debug("sharing")

  std::vector< std::queue<T> > queues;
  for(unsigned i = 0; i < numThreads; ++i){
    queues.push_back(std::queue<T>());
  }

  const unsigned int sharingBroadcastInterval = 1;

  boost::mutex mutex_activity;

  /* Disable interruption, so that we can check manually */
  boost::this_thread::disable_interruption di;

  while(not boost::this_thread::interruption_requested()) {

    boost::this_thread::sleep
      (boost::posix_time::milliseconds(sharingBroadcastInterval));

    for(unsigned t = 0; t < numThreads; ++t) {

      /* No activity on this channel */
      if(channelsOut[t]->empty()) continue;

      /* Alert if channel full, so that we increase sharingChannelSize
         or decrease sharingBroadcastInterval */
      assert(not channelsOut[t]->full());

      T data = channelsOut[t]->pop();

      if(Trace.isOn("sharing")) {
        ++cnt[t];
        Trace("sharing") << "sharing: Got data. Thread #" << t
                         << ". Chunk " << cnt[t] << std::endl;
      }

      for(unsigned u = 0; u < numThreads; ++u) {
        if(u != t){
          Trace("sharing") << "sharing: adding to queue " << u << std::endl;
          queues[u].push(data);
        }
      }/* end of inner for: broadcast activity */

    } /* end of outer for: look for activity */

    for(unsigned t = 0; t < numThreads; ++t){
      /* Alert if channel full, so that we increase sharingChannelSize
         or decrease sharingBroadcastInterval */
      assert(not channelsIn[t]->full());

      while(!queues[t].empty() && !channelsIn[t]->full()){
        Trace("sharing") << "sharing: pushing on channel " << t << std::endl;
        T data = queues[t].front();
        channelsIn[t]->push(data);
        queues[t].pop();
      }
    }
  } /* end of infinite while */

  Trace("interrupt")
    << "sharing thread interrupted, interrupting all smtEngines" << std::endl;

  for(unsigned t = 0; t < numThreads; ++t) {
    Trace("interrupt") << "Interrupting thread #" << t << std::endl;
    try{
      smts[t]->interrupt();
    }catch(ModalException &e){
      // It's fine, the thread is probably not there.
      Trace("interrupt") << "Could not interrupt thread #" << t << std::endl;
    }
  }

  Trace("sharing") << "sharing: Interrupted, exiting." << std::endl;
}/* sharingManager() */

}/* CVC4 namespace */

#endif   /* __CVC4__PORTFOLIO_UTIL_H */
