/*********************                                                        */
/*! \file IPointer.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief interface IPointer for java wrappers for corresponding c++ classes
 **/

package cvc5;

interface IPointer
{
  long getPointer();
}
