/*********************                                                        */
/*! \file set_language.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definition of input and output languages
 **
 ** Definition of input and output languages.
 **/
#include "options/set_language.h"

#include <iosfwd>
#include <iomanip>

#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"

namespace CVC4 {
namespace language {

const int SetLanguage::s_iosIndex = std::ios_base::xalloc();

SetLanguage::Scope::Scope(std::ostream& out, OutputLanguage language)
  : d_out(out)
  , d_oldLanguage(SetLanguage::getLanguage(out))
{
  SetLanguage::setLanguage(out, language);
}

SetLanguage::Scope::~Scope(){
  SetLanguage::setLanguage(d_out, d_oldLanguage);
}


SetLanguage::SetLanguage(OutputLanguage l)
  : d_language(l)
{}

void SetLanguage::applyLanguage(std::ostream& out) {
  // (offset by one to detect whether default has been set yet)
  out.iword(s_iosIndex) = int(d_language) + 1;
}

OutputLanguage SetLanguage::getLanguage(std::ostream& out) {
  long& l = out.iword(s_iosIndex);
  if(l == 0) {
    // set the default language on this ostream
    // (offset by one to detect whether default has been set yet)
    if(not Options::isCurrentNull()) {
      l = options::outputLanguage() + 1;
    }
    if(l <= 0 || l > language::output::LANG_MAX) {
      // if called from outside the library, we may not have options
      // available to us at this point (or perhaps the output language
      // is not set in Options).  Default to something reasonable, but
      // don't set "l" since that would make it "sticky" for this
      // stream.
      return OutputLanguage(s_defaultOutputLanguage);
    }
  }
  return OutputLanguage(l - 1);
}

void SetLanguage::setLanguage(std::ostream& out, OutputLanguage l) {
  // (offset by one to detect whether default has been set yet)
  out.iword(s_iosIndex) = int(l) + 1;
}

std::ostream& operator<<(std::ostream& out, SetLanguage l) {
  l.applyLanguage(out);
  return out;
}

}/* CVC4::language namespace */
}/* CVC4 namespace */
