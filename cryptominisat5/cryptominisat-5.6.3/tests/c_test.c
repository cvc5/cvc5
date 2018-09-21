/******************************************
Copyright (c) 2016, @Storyyeller

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


#include "cryptominisat5/cryptominisat_c.h"
#include "assert.h"

c_Lit new_lit(uint32_t var, bool neg) {
    c_Lit x;
    x.x = (var << 1) | neg;
    return x;
}

int main(void) {
    int new; // make sure this is actually compiled as C

    SATSolver *solver = cmsat_new();
    cmsat_set_num_threads(solver, 4);
    cmsat_new_vars(solver, 3);

    c_Lit clause[4];
    clause[0] = new_lit(0, false);
    cmsat_add_clause(solver, clause, 1);

    clause[0] = new_lit(1, true);
    cmsat_add_clause(solver, clause, 1);

    clause[0] = new_lit(0, true);
    clause[1] = new_lit(1, false);
    clause[2] = new_lit(2, false);
    cmsat_add_clause(solver, clause, 3);

    c_lbool ret = cmsat_solve(solver);
    assert(ret.x == L_TRUE);

    slice_lbool model = cmsat_get_model(solver);
    assert(model.vals[0].x == L_TRUE);
    assert(model.vals[1].x == L_FALSE);
    assert(model.vals[2].x == L_TRUE);

    cmsat_free(solver);
    return 0;
}
