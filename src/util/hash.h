/*********************                                                        */
/*! \file hash.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking
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

#include "cvc4_public.h"

#ifndef __CVC4__HASH_H
#define __CVC4__HASH_H

#include <ext/hash_map>
namespace std { using namespace __gnu_cxx; }

namespace CVC4 {

struct StringHashFunction {
  size_t operator()(const std::string& str) const {
    return std::hash<const char*>()(str.c_str());
  }
};/* struct StringHashFunction */

}/* CVC4 namespace */

#endif /* __CVC4__HASH_H */
