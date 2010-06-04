/*********************                                                        */
/*! \file parser_options.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PARSER__PARSER_OPTIONS_H
#define __CVC4__PARSER__PARSER_OPTIONS_H

namespace CVC4 {
namespace parser {

/** The input language option */
enum InputLanguage {
  /** The SMTLIB input language */
  LANG_SMTLIB,
  /** The SMTLIB v2 input language */
  LANG_SMTLIB_V2,
  /** The CVC4 input language */
  LANG_CVC4,
  /** Auto-detect the language */
  LANG_AUTO
};/* enum InputLanguage */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_OPTIONS_H */
