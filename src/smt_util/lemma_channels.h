/*********************                                                        */
/*! \file lemma_channels.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief LemmaChannels is a light container for a pair of input and output
 ** lemma channels.
 **
 ** LemmaChannels is a light container for a pair of input and output
 ** lemma channels. These contain paramaters for the infrequently
 ** used Portfolio mode. There should be exactly one of these per SmtEngine
 ** with the same lifetime as the SmtEngine. The user directly passes these as
 ** pointers and is resonsible for cleaning up the memory.
 **
 ** Basically, the problem this class is solving is that previously these were
 ** using smt_options.h and the Options class as globals for these same
 ** datastructures.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT_UTIL__LEMMA_CHANNELS_H
#define __CVC4__SMT_UTIL__LEMMA_CHANNELS_H

#include <iosfwd>
#include <string>
#include <utility>

#include "options/option_exception.h"
#include "smt_util/lemma_input_channel.h"
#include "smt_util/lemma_output_channel.h"

namespace CVC4 {

/**
 * LemmaChannels is a wrapper around two pointers:
 * - getLemmaInputChannel()
 * - getLemmaOutputChannel()
 *
 * The user can directly set these and is responsible for handling the
 * memory for these. These datastructures are used for Portfolio mode.
 */
class CVC4_PUBLIC LemmaChannels {
 public:
  /** Creates an empty LemmaChannels with all 4 pointers initially NULL. */
  LemmaChannels();
  ~LemmaChannels();

  void setLemmaInputChannel(LemmaInputChannel* in);
  LemmaInputChannel* getLemmaInputChannel() { return d_lemmaInputChannel; }

  void setLemmaOutputChannel(LemmaOutputChannel* out);
  LemmaOutputChannel* getLemmaOutputChannel() { return d_lemmaOutputChannel; }

 private:
  // Disable copy constructor.
  LemmaChannels(const LemmaChannels&) CVC4_UNDEFINED;

  // Disable assignment operator.
  LemmaChannels& operator=(const LemmaChannels&) CVC4_UNDEFINED;

  /** This captures the old options::lemmaInputChannel .*/
  LemmaInputChannel* d_lemmaInputChannel;

  /** This captures the old options::lemmaOutputChannel .*/
  LemmaOutputChannel* d_lemmaOutputChannel;
}; /* class LemmaChannels */

} /* namespace CVC4 */

#endif /* __CVC4__SMT_UTIL__LEMMA_CHANNELS_H */
