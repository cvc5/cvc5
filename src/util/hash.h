/*
 * hash.h
 *
 *  Created on: May 8, 2010
 *      Author: chris
 */

#ifndef __CVC4__HASH_H_
#define __CVC4__HASH_H_

#include <ext/hash_map>
namespace std { using namespace __gnu_cxx; }

namespace CVC4 {

struct StringHashFunction {
  size_t operator()(const std::string& str) const {
    return std::hash<const char*>()(str.c_str());
  }
};

}

#endif /* __CVC4__HASH_H_ */
