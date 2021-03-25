/*********************                                                        */
/*! \file trigger_database.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief trigger database class
 **/

#include "theory/quantifiers/ematching/trigger_database.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

TriggerDatabase::TriggerDatabase(QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr)
    : d_qs(qs), d_qim(qim), d_qreg(qr), d_treg(tr)
{
}
TriggerDatabase::~TriggerDatabase() {}

Trigger* TriggerDatabase:: ::getTrigger(std::vector<Node>& nodes)
{
  return d_trie.getTrigger(nodes);
}
void TriggerDatabase:: ::addTrigger(std::vector<Node>& nodes, Trigger* t)
{
  d_trie.addTrigger(nodes, t);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H */
