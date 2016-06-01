/*********************                                                        */
/*! \file portfolio_util.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Code relevant only for portfolio builds
 **/

#include "main/portfolio_util.h"

#include <unistd.h>

#include <cassert>
#include <vector>

#include "options/options.h"

using namespace std;

namespace CVC4 {

OptionsList::OptionsList() : d_options() {}

OptionsList::~OptionsList(){
  for(std::vector<Options*>::iterator i = d_options.begin(),
          iend = d_options.end(); i != iend; ++i)
  {
    Options* current = *i;
    delete current;
  }
  d_options.clear();
}

void OptionsList::push_back_copy(const Options& opts) {
  Options* copy = new Options;
  copy->copyValues(opts);
  d_options.push_back(copy);
}

Options& OptionsList::operator[](size_t position){
  return *(d_options[position]);
}

const Options& OptionsList::operator[](size_t position) const {
  return *(d_options[position]);
}

Options& OptionsList::back() {
  return *(d_options.back());
}

size_t OptionsList::size() const {
  return d_options.size();
}

void parseThreadSpecificOptions(OptionsList& threadOptions, const Options& opts)
{

  unsigned numThreads = opts.getThreads();

  for(unsigned i = 0; i < numThreads; ++i) {
    threadOptions.push_back_copy(opts);
    Options& tOpts = threadOptions.back();

    // Set thread identifier
    tOpts.setThreadId(i);
    const std::vector<std::string>& optThreadArgvs = opts.getThreadArgv();
    if(i < optThreadArgvs.size() && (! optThreadArgvs[i].empty())) {
      // separate out the thread's individual configuration string
      stringstream optidss;
      optidss << "--thread" << i;
      string optid = optidss.str();
      int targc = 1;
      char* tbuf = strdup(optThreadArgvs[i].c_str());
      char* p = tbuf;
      // string length is certainly an upper bound on size needed
      char** targv = new char*[optThreadArgvs[i].size()];
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
          Options::parseOptions(&tOpts, targc, targv);
        } catch(OptionException& e) {
          stringstream ss;
          ss << optid << ": " << e.getMessage();
          throw OptionException(ss.str());
        }
        if(tOpts.getThreads() != numThreads ||
           tOpts.getThreadArgv() != opts.getThreadArgv()) {
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
}

void PortfolioLemmaOutputChannel::notifyNewLemma(Expr lemma) {
  if(int(lemma.getNumChildren()) > Options::currentGetSharingFilterByLength()) {
    return;
  }
  ++cnt;
  Trace("sharing") << d_tag << ": " << lemma << std::endl;
  expr::pickle::Pickle pkl;
  try {
    d_pickler.toPickle(lemma, pkl);
    d_sharedChannel->push(pkl);
    if(Trace.isOn("showSharing") && Options::currentGetThreadId() == 0) {
      (*(Options::currentGetOut()))
          << "thread #0: notifyNewLemma: " << lemma << std::endl;
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
  if(Trace.isOn("showSharing") && Options::currentGetThreadId() == 0) {
    (*Options::currentGetOut()) << "thread #0: getNewLemma: " << e << std::endl;
  }
  return e;
}

}/*CVC4 namespace */
