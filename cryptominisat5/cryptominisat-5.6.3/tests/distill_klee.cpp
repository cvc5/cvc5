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

#include <set>
using std::set;

#include "src/solver.h"
#include "src/distillerlongwithimpl.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"
#include <klee/klee.h>

int main(int argc, char **argv)
{
    Solver* s;
    DistillerLongWithImpl* distillwbin;
    std::atomic<bool> must_inter;
    SolverConf conf;
    //conf.verbosity = 20;
    must_inter.store(false, std::memory_order_relaxed);
    s = new Solver(&conf, &must_inter);
    distillwbin = s->dist_long_with_impl;

    s->new_vars(4);
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    distillwbin->distill_long_with_implicit(false);
    //check_irred_cls_eq(s, "1, 2");

    delete s;

    return 0;
}

