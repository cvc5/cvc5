/******************************************
Copyright (c) 2014, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

// How To compile on Linux:
// 1) compile cryptominsat
// 2) install cryptominisat: sudo make install
// 3) run ldconfig: sudo ldconfig
// 4) build: g++ -std=c++11 readme_test.cpp -lcryptominisat5 -o readme_test
// 5) run: ./readme_test

#include <cryptominisat5/cryptominisat.h>
#include <cassert>
#include <vector>
using std::vector;
using namespace CMSat;

int main()
{
    SATSolver solver;
    vector<Lit> clause;

    //We need 3 variables
    solver.new_var();
    solver.new_var();
    solver.new_var();

    //adds "1 0"
    clause.push_back(Lit(0, false));
    solver.add_clause(clause);

    //adds "-1 2 3 0"
    clause.clear();
    clause.push_back(Lit(0, true));
    clause.push_back(Lit(1, false));
    clause.push_back(Lit(2, false));
    solver.add_clause(clause);

    lbool ret = l_True;
    while(ret == l_True) {
        ret = solver.solve();
        if (ret == l_True) {
            std::cout
            << "Solution is: "
            << solver.get_model()[0]
            << ", " << solver.get_model()[1]
            << ", " << solver.get_model()[2]
            << std::endl;

            clause.clear();
            for(size_t i = 0; i < 3; i++) {
                if (solver.get_model()[i] != l_Undef) {
                    clause.push_back(Lit(i, solver.get_model()[i] == l_True));
                }
            }
            solver.add_clause(clause);
        } else if (ret == l_False) {
            std::cout << "No more solutions." << std::endl;
        } else {
            std::cout << "Solver returned that it didn't finish running."
            "maybe you put a limit on its runtime?" << std::endl;
        }
    }

    return 0;
}
