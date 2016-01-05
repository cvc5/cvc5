/*********************                                                        */
/*! \file portfolio_util.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Code relevant only for portfolio builds
 **/

#include "main/portfolio_util.h"

#include <unistd.h>

#include <cassert>
#include <vector>

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/prop_options.h"
#include "options/smt_options.h"
#include "smt/smt_options_handler.h"

using namespace std;

namespace CVC4 {

vector<Options> parseThreadSpecificOptions(Options opts)
{
  vector<Options> threadOptions;

#warning "TODO: Check that the SmtEngine pointer should be NULL with Kshitij."
  smt::SmtOptionsHandler optionsHandler(NULL);

  unsigned numThreads = opts[options::threads];

  for(unsigned i = 0; i < numThreads; ++i) {
    threadOptions.push_back(opts);
    Options& tOpts = threadOptions.back();

    // Set thread identifier
    tOpts.set(options::thread_id, i);

    if(i < opts[options::threadArgv].size() &&
       !opts[options::threadArgv][i].empty()) {

      // separate out the thread's individual configuration string
      stringstream optidss;
      optidss << "--thread" << i;
      string optid = optidss.str();
      int targc = 1;
      char* tbuf = strdup(opts[options::threadArgv][i].c_str());
      char* p = tbuf;
      // string length is certainly an upper bound on size needed
      char** targv = new char*[opts[options::threadArgv][i].size()];
      char** vp = targv;
      *vp++ = strdup(optid.c_str());
      p = strtok(p, " ");
      while(p != NULL) {
        *vp++ = p;
        ++targc;
        p = strtok(NULL, " ");
      }
      *vp++ = NULL;
      if(targc > 1) { // this is necessary in case you do e.g. --thread0="  "
        try {
          tOpts.parseOptions(targc, targv, &optionsHandler);
        } catch(OptionException& e) {
          stringstream ss;
          ss << optid << ": " << e.getMessage();
          throw OptionException(ss.str());
        }
        if(optind != targc) {
          stringstream ss;
          ss << "unused argument `" << targv[optind]
             << "' in thread configuration " << optid << " !";
          throw OptionException(ss.str());
        }
        if(tOpts[options::threads] != numThreads
           || tOpts[options::threadArgv] != opts[options::threadArgv]) {
          stringstream ss;
          ss << "not allowed to set thread options in " << optid << " !";
          throw OptionException(ss.str());
        }
      }
      free(targv[0]);
      delete [] targv;
      free(tbuf);
    }
  }

  assert(numThreads >= 1);      //do we need this?

  return threadOptions;
}

void PortfolioLemmaOutputChannel::notifyNewLemma(Expr lemma) {
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


PortfolioLemmaInputChannel::PortfolioLemmaInputChannel(std::string tag,
    SharedChannel<ChannelFormat>* c,
    ExprManager* em,
    VarMap& to,
    VarMap& from)
    : d_tag(tag), d_sharedChannel(c), d_pickler(em, to, from)
{}

bool PortfolioLemmaInputChannel::hasNewLemma(){
  Debug("lemmaInputChannel") << d_tag << ": " << "hasNewLemma" << std::endl;
  return !d_sharedChannel->empty();
}

Expr PortfolioLemmaInputChannel::getNewLemma() {
  Debug("lemmaInputChannel") << d_tag << ": " << "getNewLemma" << std::endl;
  expr::pickle::Pickle pkl = d_sharedChannel->pop();

  Expr e = d_pickler.fromPickle(pkl);
  if(Trace.isOn("showSharing") && options::thread_id() == 0) {
    *options::out() << "thread #0: getNewLemma: " << e << std::endl;
  }
  return e;
}

}/*CVC4 namespace */
