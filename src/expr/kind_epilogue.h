/*********************                                           -*- C++ -*-  */
/** kind_epilogue.h
 ** Original author: 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Kinds of Nodes.
 **/

  case LAST_KIND: out << "LAST_KIND"; break;
  default: out << "UNKNOWNKIND!" << int(k); break;
  }

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__KIND_H */
