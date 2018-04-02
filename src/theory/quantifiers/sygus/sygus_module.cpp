/*********************                                                        */
/*! \file sygus_module.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_module
 **/

#include "theory/quantifiers/sygus/sygus_module.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusModule::SygusModule(QuantifiersEngine* qe, CegConjecture* p)
    : d_qe(qe), d_parent(p)
{
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
