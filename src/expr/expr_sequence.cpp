/*********************                                                        */
/*! \file sequence.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the sequence data type.
 **/

#include "expr/expr_sequence.h"

using namespace std;

namespace CVC4 {

ExprSequence::ExprSequence(Type t) : d_type(t)
{
}

const Type& ExprSequence::getType() const { return d_type; }

size_t ExprSequenceHashFunction::operator()(const ExprSequence& es) const {
  return TypeHashFunction()(es.getType());
}

std::ostream& operator<<(std::ostream& os, const Sequence& s)
{
  // FIXME
  return os << "\""
            << "\"";
}

}  // namespace CVC4
