/*********************                                           -*- C++ -*-  */
/** options.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#define __CVC4__OPTIONS_H

namespace CVC4 {

struct Options {
  std::string binary_name;

  bool smtcomp_mode;
  bool statistics;

  /* -1 means no output */
  /* 0 is normal (and default) -- warnings only */
  /* 1 is warnings + notices so the user doesn't get too bored */
  /* 2 is chatty, giving statistical things etc. */
  /* with 3, the solver is slowed down by all the scrolling */
  int verbosity;

  std::string lang;

  Options() : binary_name(),
              smtcomp_mode(false),
              statistics(false),
              verbosity(0),
              lang()
  {}
};/* struct Options */

}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS_H */
