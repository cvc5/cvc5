/*********************                                                        */
/** kind_middle.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Middle section of the Node kind header.  This file finishes off the
 ** Kind enum and starts the pretty-printing function definition.
 **/

  LAST_KIND

};/* enum Kind */

inline std::ostream& operator<<(std::ostream&, CVC4::Kind) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& out, CVC4::Kind k) {
  using namespace CVC4;

  switch(k) {

  /* special cases */
  case UNDEFINED_KIND: out << "UNDEFINED_KIND"; break;
  case NULL_EXPR: out << "NULL"; break;
