/*********************                                                        */
/*! \file equality_engine.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "equality_engine.h"

using namespace CVC4::theory::bv;

const size_t BitSizeTraits::id_null = (1u << BitSizeTraits::id_bits) - 1;
const size_t BitSizeTraits::trigger_id_null = (1u << BitSizeTraits::trigger_id_bits) - 1;


