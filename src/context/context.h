/*********************                                           -*- C++ -*-  */
/** context.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Context class and context manager.
 **/

#ifndef __CVC4__CONTEXT__CONTEXT_H
#define __CVC4__CONTEXT__CONTEXT_H

namespace CVC4 {
namespace context {

class Context;

class ContextManager {
public:
  void switchContext(Context);
  Context snapshot();
};/* class ContextManager */

class ContextObject {
public:
  void snapshot();
  void restore();
};/* class ContextObject */

template <class T>
class CDO;

template <class T>
class CDMap;

template <class T>
class CDList;

template <class T>
class CDSet;

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CONTEXT_H */
