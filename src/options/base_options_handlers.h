/*********************                                                        */
/*! \file base_options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Kshitij Bansal
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BASE_OPTIONS_HANDLERS_H
#define __CVC4__BASE_OPTIONS_HANDLERS_H

#include <iostream>
#include <string>
#include <sstream>

#include "expr/command.h"
#include "util/didyoumean.h"
#include "util/language.h"

namespace CVC4 {
namespace options {

inline void setVerbosity(std::string option, int value, SmtEngine* smt) throw(OptionException) {
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(CVC4::null_os);
    TraceChannel.setStream(CVC4::null_os);
    NoticeChannel.setStream(CVC4::null_os);
    ChatChannel.setStream(CVC4::null_os);
    MessageChannel.setStream(CVC4::null_os);
    WarningChannel.setStream(CVC4::null_os);
  } else {
    if(value < 2) {
      ChatChannel.setStream(CVC4::null_os);
    } else {
      ChatChannel.setStream(std::cout);
    }
    if(value < 1) {
      NoticeChannel.setStream(CVC4::null_os);
    } else {
      NoticeChannel.setStream(std::cout);
    }
    if(value < 0) {
      MessageChannel.setStream(CVC4::null_os);
      WarningChannel.setStream(CVC4::null_os);
    } else {
      MessageChannel.setStream(std::cout);
      WarningChannel.setStream(std::cerr);
    }
  }
}

inline void increaseVerbosity(std::string option, SmtEngine* smt) {
  options::verbosity.set(options::verbosity() + 1);
  setVerbosity(option, options::verbosity(), smt);
}

inline void decreaseVerbosity(std::string option, SmtEngine* smt) {
  options::verbosity.set(options::verbosity() - 1);
  setVerbosity(option, options::verbosity(), smt);
}

inline OutputLanguage stringToOutputLanguage(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::output::LANG_AUTO;
  }

  try {
    return language::toOutputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() + "\nTry --output-language help");
  }

  Unreachable();
}

inline InputLanguage stringToInputLanguage(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::input::LANG_AUTO;
  }

  try {
    return language::toInputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() + "\nTry --language help");
  }

  Unreachable();
}

inline std::string suggestTags(char const* const* validTags, std::string inputTag,
                               char const* const* additionalTags = NULL)
{
  DidYouMean didYouMean;

  const char* opt;
  for(size_t i = 0; (opt = validTags[i]) != NULL; ++i) {
    didYouMean.addWord(validTags[i]);
  }
  if(additionalTags != NULL) {
    for(size_t i = 0; (opt = additionalTags[i]) != NULL; ++i) {
      didYouMean.addWord(additionalTags[i]);
    }
  }

  return  didYouMean.getMatchAsString(inputTag);
}

inline void addTraceTag(std::string option, std::string optarg, SmtEngine* smt) {
  if(Configuration::isTracingBuild()) {
    if(!Configuration::isTraceTag(optarg.c_str())) {

      if(optarg == "help") {
        printf("available tags:");
        unsigned ntags = Configuration::getNumTraceTags();
        char const* const* tags = Configuration::getTraceTags();
        for(unsigned i = 0; i < ntags; ++ i) {
          printf(" %s", tags[i]);
        }
        printf("\n");
        exit(0);
      }

      throw OptionException(std::string("trace tag ") + optarg +
                            std::string(" not available.") +
                            suggestTags(Configuration::getTraceTags(), optarg) );
    }
  } else {
    throw OptionException("trace tags not available in non-tracing builds");
  }
  Trace.on(optarg);
}

inline void addDebugTag(std::string option, std::string optarg, SmtEngine* smt) {
  if(Configuration::isDebugBuild() && Configuration::isTracingBuild()) {
    if(!Configuration::isDebugTag(optarg.c_str()) &&
       !Configuration::isTraceTag(optarg.c_str())) {

      if(optarg == "help") {
        printf("available tags:");
        unsigned ntags = Configuration::getNumDebugTags();
        char const* const* tags = Configuration::getDebugTags();
        for(unsigned i = 0; i < ntags; ++ i) {
          printf(" %s", tags[i]);
        }
        printf("\n");
        exit(0);
      }

      throw OptionException(std::string("debug tag ") + optarg +
                            std::string(" not available.") +
                            suggestTags(Configuration::getDebugTags(), optarg, Configuration::getTraceTags()) );
    }
  } else if(! Configuration::isDebugBuild()) {
    throw OptionException("debug tags not available in non-debug builds");
  } else {
    throw OptionException("debug tags not available in non-tracing builds");
  }
  Debug.on(optarg);
  Trace.on(optarg);
}

inline void setPrintSuccess(std::string option, bool value, SmtEngine* smt) {
  Debug.getStream() << Command::printsuccess(value);
  Trace.getStream() << Command::printsuccess(value);
  Notice.getStream() << Command::printsuccess(value);
  Chat.getStream() << Command::printsuccess(value);
  Message.getStream() << Command::printsuccess(value);
  Warning.getStream() << Command::printsuccess(value);
  *options::out() << Command::printsuccess(value);
}

template <template <class U> class Cmp>
class comparator {
  long d_lbound;
  double d_dbound;
  bool d_hasLbound;

public:
  comparator(int i) throw() : d_lbound(i), d_dbound(0.0), d_hasLbound(true) {}
  comparator(long l) throw() : d_lbound(l), d_dbound(0.0), d_hasLbound(true) {}
  comparator(double d) throw() : d_lbound(0), d_dbound(d), d_hasLbound(false) {}

  template <class T>
  void operator()(std::string option, const T& value, SmtEngine* smt) {
    if((d_hasLbound && !(Cmp<T>()(value, T(d_lbound)))) ||
       (!d_hasLbound && !(Cmp<T>()(value, T(d_dbound))))) {
      std::stringstream ss;
      ss << option << ": " << value << " is not a legal setting";
      throw OptionException(ss.str());
    }
  }
};/* class comparator */

struct greater : public comparator<std::greater> {
  greater(int i) throw() : comparator<std::greater>(i) {}
  greater(long l) throw() : comparator<std::greater>(l) {}
  greater(double d) throw() : comparator<std::greater>(d) {}
};/* struct greater */

struct greater_equal : public comparator<std::greater_equal> {
  greater_equal(int i) throw() : comparator<std::greater_equal>(i) {}
  greater_equal(long l) throw() : comparator<std::greater_equal>(l) {}
  greater_equal(double d) throw() : comparator<std::greater_equal>(d) {}
};/* struct greater_equal */

struct less : public comparator<std::less> {
  less(int i) throw() : comparator<std::less>(i) {}
  less(long l) throw() : comparator<std::less>(l) {}
  less(double d) throw() : comparator<std::less>(d) {}
};/* struct less */

struct less_equal : public comparator<std::less_equal> {
  less_equal(int i) throw() : comparator<std::less_equal>(i) {}
  less_equal(long l) throw() : comparator<std::less_equal>(l) {}
  less_equal(double d) throw() : comparator<std::less_equal>(d) {}
};/* struct less_equal */

struct not_equal : public comparator<std::not_equal_to> {
  not_equal(int i) throw() : comparator<std::not_equal_to>(i) {}
  not_equal(long l) throw() : comparator<std::not_equal_to>(l) {}
  not_equal(double d) throw() : comparator<std::not_equal_to>(d) {}
};/* struct not_equal_to */

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__BASE_OPTIONS_HANDLERS_H */

