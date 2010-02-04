/*********************                                           -*- C++ -*-  */
/** kind_prologue.h
 ** Original author: 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Kinds of Nodes.
 **/

#ifndef __CVC4__KIND_H
#define __CVC4__KIND_H

#include "cvc4_config.h"
#include <iostream>

namespace CVC4 {

enum Kind {
  /* undefined */
  UNDEFINED_KIND = -1,
  /** Null Kind */
  NULL_EXPR,

  /* built-ins */
  EQUAL,
  ITE,
  SKOLEM,
  VARIABLE,
