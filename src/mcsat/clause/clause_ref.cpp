#include "clause_ref.h"
#include "clause_db.h"

using namespace CVC4;
using namespace mcsat;

const CRef CRef::null;

void CRef::toStream(std::ostream& out) const {
  return getClause().toStream(out);
}

Clause& CRef::getClause() const {
  Assert(hasClause());
  return ClauseFarm::getCurrent()->getClauseDB(d_db).getClause(*this);
}

