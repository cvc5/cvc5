#pragma once

#include "cvc4_private.h"

#include "expr/node.h"
#include "context/cdlist.h"
#include "context/cdhashset.h"

#include "mcsat/variable/variable.h"
#include "mcsat/variable/variable_db.h"
#include "mcsat/clause/literal.h"

#include <ext/hash_map>

namespace CVC4 {
namespace mcsat {

class CnfOutputListener {
public:

  virtual ~CnfOutputListener() {}

  /** Notification of a new clause */
  virtual void newClause(LiteralVector& clause) = 0;
};

class CnfStream {

public:

  /** Destructor */
  virtual ~CnfStream() {}

  /**
   * Add a listener to this CNF transform.
   */
  void addOutputListener(CnfOutputListener* cnfListener) {
    d_outputNotifyList.push_back(cnfListener);
  }

  /**
   * Converts the formula to CNF.
   * @param node node to convert and assert
   * @param negated whether we are asserting the node negated
   */
  virtual void convert(TNode node, bool negated) = 0;

private:

  /** Who gets the output of the CNF */
  std::vector<CnfOutputListener*> d_outputNotifyList;

protected:
  
  /**
   * Output the clause.
   */
  void outputClause(LiteralVector& clause);

  /**
   * Output the unit clause.
   */
  void outputClause(Literal a);

  /**
   * Output the binary clause.
   */
  void outputClause(Literal a, Literal b);

  /**
   * Ouput the ternary clause.
   */
  void outputClause(Literal a, Literal b, Literal c);

  /**
   * Constructs a new literal for an atom and returns it.
   */
  Literal convertAtom(TNode node);

};/* class CnfStream */

}/* mcsat namespace */
}/* CVC4 namespace */
