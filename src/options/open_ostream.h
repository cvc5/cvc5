/*********************                                                        */
/*! \file open_ostream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__OPEN_OSTREAM_H
#define CVC4__OPEN_OSTREAM_H

#include <map>
#include <ostream>
#include <string>
#include <utility>

#include "options/option_exception.h"

namespace CVC4 {

class OstreamOpener {
 public:
  OstreamOpener(const char* channelName);

  void addSpecialCase(const std::string& name, std::ostream* out);

  /**
   * If name == "", this throws OptionException with the message, messageIfEmpty.
   * If name is a special case, this return <false, out> where out is the
   *   special case that was added.
   * If name == "std::cerr", this return <false, &cerr>.
   * If none of the previous conditions hold and !options::filesystemAccess(),
   *   this throws an OptionException.
   * Otherwise, this attempts to open a ofstream using the filename, name.
   *   If this fails, this throws and OptionException. If this succeeds, this
   *   returns <true, stream> where stream is a ostream allocated by new.
   *   The caller is in this case the owner of the allocated memory.
   */
  std::pair<bool, std::ostream*> open(const std::string& name) const;

 private:
  const char* d_channelName;
  std::map< std::string, std::ostream* > d_specialCases;

}; /* class OstreamOpener */

std::string cvc4_errno_failreason();

}/* CVC4 namespace */

#endif /* CVC4__OPEN_OSTREAM_H */
