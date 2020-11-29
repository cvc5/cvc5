/*********************                                                        */
/*! \file set_language.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
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

#include "cvc4_public.h"

#ifndef CVC4__OPTIONS__SET_LANGUAGE_H
#define CVC4__OPTIONS__SET_LANGUAGE_H

#include <iostream>
#include "options/language.h"

namespace CVC4 {
namespace language {

/**
 * IOStream manipulator to set the output language for Exprs.
 */
class CVC4_PUBLIC SetLanguage {
public:
  /**
   * Set a language on the output stream for the current stack scope.
   * This makes sure the old language is reset on the stream after
   * normal OR exceptional exit from the scope, using the RAII C++
   * idiom.
   */
  class Scope {
   public:
    Scope(std::ostream& out, OutputLanguage language);
    ~Scope();
   private:
    std::ostream& d_out;
    OutputLanguage d_oldLanguage;
  };/* class SetLanguage::Scope */

  /**
   * Construct a ExprSetLanguage with the given setting.
   */
  SetLanguage(OutputLanguage l);

  void applyLanguage(std::ostream& out);

  static OutputLanguage getLanguage(std::ostream& out);

  static void setLanguage(std::ostream& out, OutputLanguage l);

private:

  /**
   * The allocated index in ios_base for our depth setting.
   */
  static const int s_iosIndex;

  /**
   * The default language to use, for ostreams that haven't yet had a
   * setlanguage() applied to them and where the current Options
   * information isn't available.
   */
  static const int s_defaultOutputLanguage = language::output::LANG_AUTO;

  /**
   * When this manipulator is used, the setting is stored here.
   */
  OutputLanguage d_language;
};/* class SetLanguage */


/**
 * Sets the output language when pretty-printing a Expr to an ostream.
 * This is used liek this:
 *
 *   // let out be an ostream, e an Expr
 *   out << language::SetLanguage(LANG_SMTLIB_V2_5) << e << endl;
 *
 * This used to be used like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::setlanguage(LANG_SMTLIB_V2_5) << e << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
std::ostream& operator<<(std::ostream& out, SetLanguage l) CVC4_PUBLIC;

}/* CVC4::language namespace */
}/* CVC4 namespace */

#endif /* CVC4__OPTIONS__SET_LANGUAGE_H */
