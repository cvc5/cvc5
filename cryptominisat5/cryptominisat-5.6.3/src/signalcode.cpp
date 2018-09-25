/*
Copyright (c) 2010-2015 Mate Soos
Copyright (c) Kuldeep S. Meel, Daniel J. Fremont

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
*/

#include "signalcode.h"
#include "cryptominisat5/cryptominisat.h"
#if !defined (_MSC_VER)
#include <unistd.h>
#endif


using namespace CMSat;

SATSolver* solverToInterrupt;
int need_clean_exit;
std::string redDumpFname;
std::string irredDumpFname;

using std::cout;
using std::endl;

void SIGINT_handler(int)
{
    SATSolver* solver = solverToInterrupt;
    cout << "c " << endl;
    std::cerr << "*** INTERRUPTED ***" << endl;
    if (!redDumpFname.empty() || !irredDumpFname.empty() || need_clean_exit) {
        solver->interrupt_asap();
        std::cerr
        << "*** Please wait. We need to interrupt cleanly" << endl
        << "*** This means we might need to finish some calculations"
        << endl;
    } else {
        if (solver->nVars() > 0) {
            //if (conf.verbosity) {
                solver->add_in_partial_solving_stats();
                solver->print_stats();
            //}
        } else {
            cout
            << "No clauses or variables were put into the solver, exiting without stats"
            << endl;
        }
        #if defined (_MSC_VER)
        exit(1);
        #else
        _exit(1);
        #endif
    }
}
