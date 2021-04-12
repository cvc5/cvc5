/*********************                                                        */
/*! \file CVC5ApiRecoverableException.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class CVC5ApiRecoverableException for cvc5 recoverable API exceptions
 **/


package cvc5;

public class CVC5ApiRecoverableException extends CVC5ApiException
{
  public CVC5ApiRecoverableException(String message)
  {
    super(message);
  }
}
