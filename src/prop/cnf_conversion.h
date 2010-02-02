/*********************                                           -*- C++ -*-  */
/** cnf_conversion.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A type for describing possible CNF conversions.
 **/

#ifndef __CVC4__CNF_CONVERSION_H
#define __CVC4__CNF_CONVERSION_H

namespace CVC4 {

enum CnfConversion {
  /** TODO: explanation of DIRECT_EXPONENTIAL (is this implemented?) */
  CNF_DIRECT_EXPONENTIAL = 0,
  /** Explanation of CNF_VAR_INTRODUCTION */
  CNF_VAR_INTRODUCTION = 1
};

inline std::ostream& operator<<(std::ostream&, CVC4::CnfConversion) CVC4_PUBLIC;

inline std::ostream& operator<<(std::ostream& out, CVC4::CnfConversion c) {
  using namespace CVC4;

  switch(c) {
  case CNF_DIRECT_EXPONENTIAL:
    out << "CNF_DIRECT_EXPONENTIAL";
    break;
  case CNF_VAR_INTRODUCTION:
    out << "CNF_VAR_INTRODUCTION";
    break;
  default:
    out << "UNKNOWN-CONVERTER!" << int(c);
  }

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__CNF_CONVERSION_H */
