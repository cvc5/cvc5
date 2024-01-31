#include <cstddef>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <istream>
#include <map>
#include <set>
#include <sstream>
#include <string>

#define FAIL                           \
  {                                    \
    std::cout << "false" << std::endl; \
    return 1;                          \
  }

void next_line(std::istream& in, std::stringstream& line)
{
  std::string str;
  while (1)
  {
    std::getline(in, str);
    if (str[0] != 'p' and str[0] != 'c')
    {
      line.clear();
      line.str(str);
      break;
    }
  }
}

int main()
{
  std::string line;
  std::getline(std::cin, line);
  if (line != "(")
  {
    FAIL;
  }

  // The line listing the clauses in ALF mapping
  std::string alf_line;
  std::getline(std::cin, alf_line);
  if (alf_line[0] != '"' || alf_line[alf_line.length() - 1] != '"')
  {
    FAIL;
  }
  alf_line = alf_line.substr(1, alf_line.length() - 1);
  std::stringstream alf_stream(alf_line);

  // Line with the input file
  std::string input_line;
  std::getline(std::cin, input_line);
  if (input_line[0] != '"' || input_line[input_line.length() - 1] != '"')
  {
    FAIL;
  }
  input_line = input_line.substr(1, input_line.length() - 2);
  std::ifstream input_file;
  input_file.open(input_line);
  if (!input_file.is_open())
  {
    FAIL;
  }

  /*
      The map `alf_to_dimacs` maps alf variables to dimacs variables.
      However, when an alf variable is fresh, it could also happen that
      the mapped dimacs variables is already in use.  This case is catched
      by the `known_dimacs` set.
  */
  std::map<uint, uint> alf_to_dimacs;
  std::set<uint> known_dimacs;

  std::stringstream dimacs_line;
  next_line(input_file, dimacs_line);

  int alf_int, dimacs_int;
  while (1)
  {
    // Read next literals and handle reading failures
    bool fail = !(alf_stream >> alf_int);
    if (!(dimacs_line >> dimacs_int))
    {
      // Both ended at the same time.
      /*
          TODO: this could also be a syntax error  at the same time.
          However, this likely doesn't matter, since drat-trim would
          fail.
      */
      if (fail)
      {
        std::cout << "true" << std::endl;
        return 0;
      }
      FAIL;
    }

    // End of clause
    if (dimacs_int == 0)
    {
      if (alf_int != 0)
      {
        FAIL;
      }
      next_line(input_file, dimacs_line);
      continue;
    }
    // Polarity
    if ((alf_int < 0 && dimacs_int > 0) || (alf_int > 0 && dimacs_int < 0))
    {
      FAIL;
    }
    alf_int = abs(alf_int);
    dimacs_int = abs(dimacs_int);

    auto mapped = alf_to_dimacs.find(alf_int);
    if (mapped != alf_to_dimacs.end())
    {
      if (mapped->second != dimacs_int)
      {
        FAIL;
      }
      continue;
    }
    else
    {
      if (known_dimacs.count(dimacs_int) > 0)
      {
        FAIL;
      }
      alf_to_dimacs.insert(std::pair<int, int>(alf_int, dimacs_int));
      known_dimacs.insert(dimacs_int);
      continue;
    }
  }

  std::getline(std::cin, line);
  if (line != ")")
  {
    FAIL;
  }

  std::cout << "true" << std::endl;
  return 0;
}
