/*********************                                                        */
/*! \file cdmaybe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A context-dependent "maybe" template type
 **
 ** This implements a CDMaybe.
 ** This has either been set in the context or it has not.
 ** Template parameter T must have a default constructor and support
 ** assignment.
 **/

#include "cvc4_private.h"

#pragma once

#include "context/cdo.h"
#include "context/context.h"

namespace CVC4 {
namespace context {

class CDRaised {
private:
  context::CDO<bool> d_flag;

public:
 CDRaised(context::Context* c)
 : d_flag(c, false)
 {}


  bool isRaised() const {
    return d_flag.get();
  }

  void raise(){
    Assert(!isRaised());
    d_flag.set(true);
  }

};/* class CDRaised */

template <class T>
class CDMaybe {
private:
  typedef std::pair<bool, T> BoolTPair;
  context::CDO<BoolTPair> d_data;

public:
  CDMaybe(context::Context* c) : d_data(c, std::make_pair(false, T()))
  {}

  bool isSet() const {
    return d_data.get().first;
  }

  void set(const T& d){
    Assert(!isSet());
    d_data.set(std::make_pair(true, d));
  }

  const T& get() const{
    Assert(isSet());
    return d_data.get().second;
  }
};/* class CDMaybe<T> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

