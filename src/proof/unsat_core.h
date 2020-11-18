/*********************                                                        */
/*! \file unsat_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__UNSAT_CORE_H
#define CVC4__UNSAT_CORE_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace CVC4 {


class UnsatCore
{
public:
 UnsatCore() {}

 UnsatCore(const std::vector<Node>& core,
           std::vector<std::string>& names,
           bool useNames);
 ~UnsatCore() {}

 /** Whether we are using names for this unsat core */
 bool usingNames() const { return d_useNames; }
 /** Get the number of assertions in the unsat core */
 size_t size() const { return d_core.size(); }
 /** Get the assertions in the unsat core */
 const std::vector<Node>& getCore() const;
 /** Get their names */
 const std::vector<std::string>& getCoreNames() const;

 typedef std::vector<Node>::const_iterator iterator;
 typedef std::vector<Node>::const_iterator const_iterator;

 const_iterator begin() const;
 const_iterator end() const;

 /**
  * prints this UnsatCore object to the stream out.
  * We use the expression names stored in the SymbolManager d_sm
  */
 void toStream(std::ostream& out) const;

private:
 /** Whether we are using names for this unsat core */
 bool d_useNames;
 /** The unsat core */
 std::vector<Node> d_core;
 /** The names of assertions in the above core */
 std::vector<std::string> d_names;
};/* class UnsatCore */

/** Print the unsat core to stream out */
std::ostream& operator<<(std::ostream& out, const UnsatCore& core);

}/* CVC4 namespace */

#endif /* CVC4__UNSAT_CORE_H */
