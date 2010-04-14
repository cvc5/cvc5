/*
 * type_constant.h
 *
 *  Created on: Apr 5, 2010
 *      Author: dejan
 */

#ifndef __CVC4__TYPE_CONSTANT_H_
#define __CVC4__TYPE_CONSTANT_H_

namespace CVC4 {

enum TypeConstant {
  BOOLEAN_TYPE,
  KIND_TYPE
};

struct TypeConstantHashStrategy {
  static inline size_t hash(TypeConstant tc) {
    return tc;
  }
};/* struct BoolHashStrategy */

}

#endif /* __CVC4__TYPE_CONSTANT_H_ */
