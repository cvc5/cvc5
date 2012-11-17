/*********************                                                        */
/*! \file java_output_stream_adapter.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An OutputStream adapter for the Java bindings
 **
 ** An OutputStream adapter for the Java bindings.  This works with a lot
 ** of help from SWIG, and custom typemaps in the ".i" SWIG interface files
 ** for CVC4.  The basic idea is that, when a CVC4 function with a
 ** std::ostream& parameter is called, a Java-side binding is generated
 ** taking a java.io.OutputStream.  Now, the problem is that std::ostream
 ** has no Java equivalent, and java.io.OutputStream has no C++ equivalent,
 ** so we use this class (which exists on both sides) as the go-between.
 ** The wrapper connecting the Java function (taking an OutputStream) and
 ** the C++ function (taking an ostream) creates a JavaOutputStreamAdapter,
 ** and call the C++ function with the stringstream inside.  After the call,
 ** the generated stream material is collected and output to the Java-side
 ** OutputStream.
 **/

// private to the bindings layer
#ifndef SWIGJAVA
#  error This should only be included from the Java bindings layer.
#endif /* SWIGJAVA */

#ifndef __CVC4__BINDINGS__JAVA_OUTPUT_STREAM_ADAPTER_H
#define __CVC4__BINDINGS__JAVA_OUTPUT_STREAM_ADAPTER_H

namespace CVC4 {

class JavaOutputStreamAdapter {
  std::stringstream d_ss;

public:
  JavaOutputStreamAdapter() { }

  std::string toString() { return d_ss.str(); }

};/* class JavaOutputStreamAdapter */

}/* CVC4 namespace */

#endif /* __CVC4__BINDINGS__JAVA_OUTPUT_STREAM_ADAPTER_H */
