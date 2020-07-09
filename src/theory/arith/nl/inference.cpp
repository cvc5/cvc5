/*********************                                                        */
/*! \file inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference enumeration.
 **/

#include "theory/arith/nl/inference.h"


namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

const char* toString(Inference i)
{
  switch (i)
  {
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Inference i)
{
  out << toString(i);
  return out;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
