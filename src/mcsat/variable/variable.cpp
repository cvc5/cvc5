#include "variable.h"
#include "variable_db.h"

using namespace CVC4;
using namespace CVC4::mcsat;

const Variable Variable::null;

TNode Variable::getNode() const {
  return VariableDatabase::getCurrentDB()->getNode(*this);
}

TypeNode Variable::getTypeNode() const {
  return VariableDatabase::getCurrentDB()->getTypeNode(*this);
}

void Variable::toStream(std::ostream& out) const {

  if (isNull()) {
    out << "null";
    return;
  }

  // Get the node
  TNode node = getNode();

  // If the node is not null that's what we output
  if (!node.isNull()) {
    out << node;
    return;
  }

  /** Internal variable */
  out << "m" << d_varId;
}

