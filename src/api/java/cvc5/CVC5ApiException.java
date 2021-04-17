/*********************                                                        */
/*! \file CVC5ApiException.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class CVC5ApiException for cvc5 API exceptions
 **/

package cvc5;

public class CVC5ApiException extends Exception
{
  public CVC5ApiException(String message)
  {
    super(message);
  }
}
