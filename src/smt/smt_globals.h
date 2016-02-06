/*********************                                                        */
/*! \file smt_globals.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2015  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SmtGlobals is a light container for psuedo-global datastructures
 ** that are set by the user.
 **
 ** SmtGlobals is a light container for psuedo-global datastructures
 ** that are set by the user. These contain paramaters for infrequently
 ** used modes: Portfolio and Replay. There should be exactly one of these
 ** per SmtEngine with the same lifetime as the SmtEngine.
 ** A user directly passes these as pointers and is resonsible for cleaning up
 ** the memory.
 **
 ** Basically, the problem this class is solving is that previously these were
 ** using smt_options.h and the Options class as globals for these same
 ** datastructures.
 **
 ** This class is NOT a good long term solution, but is a reasonable stop gap.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT__SMT_GLOBALS_H
#define __CVC4__SMT__SMT_GLOBALS_H

#include <iosfwd>
#include <string>
#include <utility>

#include "expr/expr_stream.h"
#include "options/option_exception.h"
#include "smt_util/lemma_input_channel.h"
#include "smt_util/lemma_output_channel.h"

namespace CVC4 {

/**
 * SmtGlobals is a wrapper around 4 pointers:
 * - getReplayLog()
 * - getReplayStream()
 * - getLemmaInputChannel()
 * - getLemmaOutputChannel()
 *
 * The user can directly set these and is responsible for handling the
 * memory for these. These datastructures are used for the Replay and Portfolio
 * modes.
 */
class CVC4_PUBLIC SmtGlobals {
 public:
  /** Creates an empty SmtGlobals with all 4 pointers initially NULL. */
  SmtGlobals();
  ~SmtGlobals();

  /** This setsReplayLog based on --replay-log */
  void parseReplayLog(std::string optarg) throw (OptionException);
  void setReplayLog(std::ostream*);
  std::ostream* getReplayLog() { return d_replayLog; }

  void setReplayStream(ExprStream* stream);
  ExprStream* getReplayStream() { return d_replayStream; }

  void setLemmaInputChannel(LemmaInputChannel* in);
  LemmaInputChannel* getLemmaInputChannel() { return d_lemmaInputChannel; }

  void setLemmaOutputChannel(LemmaOutputChannel* out);
  LemmaOutputChannel* getLemmaOutputChannel() { return d_lemmaOutputChannel; }

 private:
  // Disable copy constructor.
  SmtGlobals(const SmtGlobals&) CVC4_UNDEFINED;

  // Disable assignment operator.
  SmtGlobals& operator=(const SmtGlobals&) CVC4_UNDEFINED;

  static std::pair<bool, std::ostream*>
      checkReplayLogFilename(std::string optarg) throw (OptionException);

  /**
   * d_gcReplayLog is true iff d_replayLog was allocated by parseReplayLog.
   */
  bool d_gcReplayLog;

  /** This captures the old options::replayLog .*/
  std::ostream* d_replayLog;

  /** This captures the old options::replayStream .*/
  ExprStream* d_replayStream;

  /** This captures the old options::lemmaInputChannel .*/
  LemmaInputChannel* d_lemmaInputChannel;

  /** This captures the old options::lemmaOutputChannel .*/
  LemmaOutputChannel* d_lemmaOutputChannel;
}; /* class SmtGlobals */

} /* namespace CVC4 */

#endif /* __CVC4__SMT__SMT_GLOBALS_H */
