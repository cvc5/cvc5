#include "theory/theory_id.h"

namespace CVC4 {
namespace theory {

TheoryId& operator++(TheoryId& id)
{
  return id = static_cast<TheoryId>(static_cast<int>(id) + 1);
}

std::ostream& operator<<(std::ostream& out, TheoryId theoryId)
{
  switch (theoryId)
  {
    case THEORY_BUILTIN: out << "THEORY_BUILTIN"; break;
    case THEORY_BOOL: out << "THEORY_BOOL"; break;
    case THEORY_UF: out << "THEORY_UF"; break;
    case THEORY_ARITH: out << "THEORY_ARITH"; break;
    case THEORY_BV: out << "THEORY_BV"; break;
    case THEORY_FP: out << "THEORY_FP"; break;
    case THEORY_ARRAYS: out << "THEORY_ARRAYS"; break;
    case THEORY_DATATYPES: out << "THEORY_DATATYPES"; break;
    case THEORY_SEP: out << "THEORY_SEP"; break;
    case THEORY_SETS: out << "THEORY_SETS"; break;
    case THEORY_STRINGS: out << "THEORY_STRINGS"; break;
    case THEORY_QUANTIFIERS: out << "THEORY_QUANTIFIERS"; break;

    default: out << "UNKNOWN_THEORY"; break;
  }
  return out;
}

std::string getStatsPrefix(TheoryId theoryId)
{
  switch (theoryId)
  {
    case THEORY_BUILTIN: return "theory::builtin"; break;
    case THEORY_BOOL: return "theory::bool"; break;
    case THEORY_UF: return "theory::uf"; break;
    case THEORY_ARITH: return "theory::arith"; break;
    case THEORY_BV: return "theory::bv"; break;
    case THEORY_FP: return "theory::fp"; break;
    case THEORY_ARRAYS: return "theory::arrays"; break;
    case THEORY_DATATYPES: return "theory::datatypes"; break;
    case THEORY_SEP: return "theory::sep"; break;
    case THEORY_SETS: return "theory::sets"; break;
    case THEORY_STRINGS: return "theory::strings"; break;
    case THEORY_QUANTIFIERS: return "theory::quantifiers"; break;

    default: break;
  }
  return "unknown";
}

}  // namespace theory
}  // namespace CVC4
