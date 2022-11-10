#include <string>

#include "proof/drat/drat_proof.h"
#include "test.h"

namespace cvc5::internal {
using namespace cvc5::internal::proof;

namespace test {

class TestDratProof : public TestInternal
{
};

TEST_F(TestDratProof, ident_sanitize)
{
  std::vector<DratInstruction> instructions = {
      DratInstruction(ADDITION,
                      prop::SatClause{prop::SatLiteral(14, true),
                                      prop::SatLiteral(29, true),
                                      prop::SatLiteral(9, false)}),
      DratInstruction(ADDITION,
                      prop::SatClause{prop::SatLiteral(18, true),
                                      prop::SatLiteral(20, false),
                                      prop::SatLiteral(30, true),
                                      prop::SatLiteral(19, false)}),
      DratInstruction(ADDITION,
                      prop::SatClause{prop::SatLiteral(28, true),
                                      prop::SatLiteral(30, false),
                                      prop::SatLiteral(13, false)}),
      DratInstruction(ADDITION,
                      prop::SatClause{prop::SatLiteral(28, true),
                                      prop::SatLiteral(30, false),
                                      prop::SatLiteral(13, false)}),
      DratInstruction(DELETION,
                      prop::SatClause{prop::SatLiteral(28, true),
                                      prop::SatLiteral(30, false),
                                      prop::SatLiteral(13, false)}),
  };
  std::string dratStr =
      "-14 -29 9 0\n-18 20 -30 19 0\n-28 30 13 0\n-28 30 13 0\nd -28 30 13 0";
  std::string fileName = "temp_drat_unit_test.drat";
  std::ofstream tempFile(fileName);
  tempFile << dratStr;
  tempFile.close();
  std::ifstream dratFileStream(fileName);
  DratProof dratProof = DratProof::fromPlain(dratFileStream);
  for (int i = 0, lenght = instructions.size(); i < lenght; i++)
  {
    ASSERT_EQ(instructions[i].d_clause,
              dratProof.getInstructions()[i].d_clause);
    ASSERT_EQ(instructions[i].d_kind, dratProof.getInstructions()[i].d_kind);
  }
  std::remove(fileName.c_str());
}

}  // namespace test
}  // namespace cvc5::internal
