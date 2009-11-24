/*********************                                           -*- C++ -*-  */
/** language.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Input languages.
 **/

#ifndef __CVC4__PARSER__LANGUAGE_H
#define __CVC4__PARSER__LANGUAGE_H

#include "util/exception.h"
#include "parser/language.h"

namespace CVC4 {
namespace parser {

enum Language {
  AUTO = 0,
  PL,
  SMTLIB,
};/* enum Language */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__LANGUAGE_H */
