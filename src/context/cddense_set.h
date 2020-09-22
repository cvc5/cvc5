/*********************                                                        */
/*! \file cddense_set.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is an abstraction of a set of unsigned integers.
 **
 ** This is an abstraction of a set of unsigned integers.
 ** This class is designed to provide constant time insertion, element_of,
 ** and fast iteration. This is done by storing backing vectors of size greater than
 ** the maximum key.
 **/

#include "cvc4_private.h"

#pragma once

#include <vector>

#include "context/context.h"
#include "context/cdlist_forward.h"
#include "context/cdlist.h"

#include "util/index.h"

namespace CVC4 {
namespace context {

template <class CleanUp = DefaultCleanUp<Index> >
class CDDenseSet {
public:
  typedef Index Element;

private:

  class RemoveIntCleanup {
  private:
    std::vector<bool>& d_set;

    /**
     * The CleanUp functor.
     */
    CleanUp d_cleanUp;
  public:
    RemoveIntCleanup(std::vector<bool>& set, const CleanUp& cleanup)
      : d_set(set), d_cleanUp(cleanup)
    {}

    void operator()(Element* p){
      d_cleanup(p);

      ArithVar x = *p;
      Assert(d_set[x]);
      d_set[x] = false;
    }
  };

  typedef CDList<Element, RemoveIntCleanup> ElementList;
  ElementList d_list;

  std::vector<bool> d_set;

public:
  typedef ElementList::const_iterator const_iterator;

  CDDenseSet(context::Context* c, const CleanUp& cleanup = CleanUp())
    : d_set(), d_list(c, true, RemoveIntCleanup(d_set, cleanup))
  { }

  /** This cannot be const as garbage collection is done lazily. */
  bool contains(Element x) const{
    if(x < d_set.size()){
      return d_set[x];
    }else{
      return false;
    }
  }

  void insert(Element x){
    Assert(!contains(x));
    if(x >= d_set.size()){
      d_set.resize(x+1, false);
    }
    d_list.push_back(x);
    d_set[x] = true;
  }

  const_iterator begin() const { return d_list.begin(); }
  const_iterator end() const { return d_list.end(); }

};/* class CDDenseSet<> */


}/* CVC4::context namespace */
}/* CVC4 namespace */
