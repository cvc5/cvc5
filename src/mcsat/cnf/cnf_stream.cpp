#include "cnf_stream.h"

using namespace std;

using namespace CVC4;
using namespace mcsat;

void CnfStream::outputClause(LiteralVector& c) {
  Debug("mcsat::cnf") << "CNF Output " << c << endl;
  for (unsigned i = 0; i < d_outputNotifyList.size(); ++ i) {
    d_outputNotifyList[i]->newClause(c);
  }
}

void CnfStream::outputClause(Literal a) {
  LiteralVector clause(1);
  clause[0] = a;
  outputClause(clause);
}

void CnfStream::outputClause(Literal a, Literal b) {
  LiteralVector clause(2);
  clause[0] = a;
  clause[1] = b;
  outputClause(clause);
}

void CnfStream::outputClause(Literal a, Literal b, Literal c) {
  LiteralVector clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  outputClause(clause);
}

Literal CnfStream::convertAtom(TNode node) {
  Debug("mcsat::cnf") << "convertAtom(" << node << ")" << endl;

  // Return the resulting literal
  return Literal(VariableDatabase::getCurrentDB()->getVariable(node), false);
}

