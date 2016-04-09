/*********************                                                        */
/*! \file lemma_channels.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This class is a light container for globals that used to live
 ** in options. This is NOT a good long term solution, but is a reasonable
 ** stop gap.
 **
 ** This class is a light container for globals that used to live
 ** in options. This is NOT a good long term solution, but is a reasonable
 ** stop gap.
 **/

#include "smt_util/lemma_channels.h"

#include <cerrno>
#include <iostream>
#include <string>
#include <utility>

#include "cvc4autoconfig.h" // Needed for CVC4_REPLAY
#include "expr/expr_stream.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/parser_options.h"
#include "smt_util/lemma_input_channel.h"
#include "smt_util/lemma_output_channel.h"

namespace CVC4 {

LemmaChannels::LemmaChannels()
    : d_lemmaInputChannel(NULL)
    , d_lemmaOutputChannel(NULL)
{}

LemmaChannels::~LemmaChannels(){}

void LemmaChannels::setLemmaInputChannel(LemmaInputChannel* in) {
  d_lemmaInputChannel = in;
}

void LemmaChannels::setLemmaOutputChannel(LemmaOutputChannel* out) {
  d_lemmaOutputChannel = out;
}


} /* namespace CVC4 */
