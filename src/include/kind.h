/*********************                                           -*- C++ -*-  */
/** expr_manager.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_EXPR_MANAGER_H
#define __CVC4_EXPR_MANAGER_H

namespace CVC4 {

enum Kind {
  AND,
  OR,
  XOR,
  NOT,
  PLUS,
  MINUS,
  UMINUS,
  
};
