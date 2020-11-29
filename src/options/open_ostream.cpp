/*********************                                                        */
/*! \file open_ostream.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
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

#include "options/open_ostream.h"


#include <cerrno>
#include <iostream>
#include <ostream>
#include <sstream>
#include <string>
#include <utility>

#include "lib/strtok_r.h"
#include "options/parser_options.h"

namespace CVC4 {

OstreamOpener::OstreamOpener(const char* channelName)
    : d_channelName(channelName)
    , d_specialCases()
{}

void OstreamOpener::addSpecialCase(const std::string& name, std::ostream* out){
  d_specialCases[name] = out;
}



std::pair< bool, std::ostream* > OstreamOpener::open(const std::string& optarg) const
{
  if(optarg == "") {
    std::stringstream ss;
    ss << "Bad file name setting for " << d_channelName;
    throw OptionException(ss.str());
  }
  if(d_specialCases.find(optarg) != d_specialCases.end()){
    return std::make_pair(false, (*d_specialCases.find(optarg)).second);
  } else if(!options::filesystemAccess()) {
    throw OptionException(std::string("Filesystem access not permitted"));
  } else {
    errno = 0;
    std::ostream* outStream;
    outStream = new std::ofstream(optarg.c_str(),
                                    std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open " << d_channelName << " file: `"
         << optarg << "': " << cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
    return make_pair(true, outStream);
  }
}

std::string cvc4_errno_failreason() {
#if HAVE_STRERROR_R
#if STRERROR_R_CHAR_P
  if(errno != 0) {
    // GNU version of strerror_r: *might* use the given buffer,
    // or might not.  It returns a pointer to buf, or not.
    char buf[80];
    return std::string(strerror_r(errno, buf, sizeof buf));
  } else {
    return "unknown reason";
  }
#else /* STRERROR_R_CHAR_P */
  if(errno != 0) {
    // XSI version of strerror_r: always uses the given buffer.
    // Returns an error code.
    char buf[80];
    if(strerror_r(errno, buf, sizeof buf) == 0) {
      return std::string(buf);
    } else {
      // some error occurred while getting the error string
      return "unknown reason";
    }
  } else {
    return "unknown reason";
  }
#endif /* STRERROR_R_CHAR_P */
#else /* HAVE_STRERROR_R */
  return "unknown reason";
#endif /* HAVE_STRERROR_R */
}

}/* CVC4 namespace */
