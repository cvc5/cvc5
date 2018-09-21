/******************************************
Copyright (c) 2016, Mate Soos

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

#ifndef __CLAUSEDUMPER_H__
#define __CLAUSEDUMPER_H__

#include <fstream>
#include <vector>
#include <limits>
#include "cryptominisat5/solvertypesmini.h"
#include "cloffset.h"

using std::vector;

namespace CMSat {

class Solver;

class ClauseDumper
{
public:
    explicit ClauseDumper(const Solver* _solver) :
        solver(_solver)
    {}

    ~ClauseDumper() {
        if (outfile) {
            outfile->close();
            delete outfile;
        }
    }

    void open_file_and_write_unsat(const std::string& fname);
    void open_file_and_write_sat(const std::string& fname);
    void open_file_and_dump_irred_clauses_preprocessor(const std::string& fname);
    void open_file_and_dump_irred_clauses(const std::string& fname);
    void open_file_and_dump_red_clauses(const std::string& fname);


private:
    const Solver* solver;
    std::ofstream* outfile = NULL;

    void write_unsat_file();
    void dump_irred_cls_for_preprocessor(bool outer_number);
    void open_dump_file(const std::string& filename);
    void dump_bin_cls(
        const bool dumpRed
        , const bool dumpIrred
        , const bool outer_number
    );

    void dump_red_cls(bool outer_numbering);
    void dump_eq_lits(bool outer_numbering);
    void dump_unit_cls(bool outer_numbering);
    void dump_blocked_clauses(bool outer_numbering);
    void dump_irred_cls(bool outer_numbering);
    void dump_component_clauses(bool outer_numbering);
    void dump_vars_appearing_inverted(bool outer_numbering);
    void dump_clauses(
        const vector<ClOffset>& cls
        , const bool outer_number
    );

    vector<Lit> tmpCl;

};

}

#endif //__CLAUSEDUMPER_H__
