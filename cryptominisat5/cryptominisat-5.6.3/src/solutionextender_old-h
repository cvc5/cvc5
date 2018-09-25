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

#ifndef __SOLUTIONEXTENDER_H__
#define __SOLUTIONEXTENDER_H__

#include "solvertypes.h"
#include "clause.h"
#include "watcharray.h"

namespace CMSat {

#ifdef VERBOSE_DEBUG
#define VERBOSE_DEBUG_RECONSTRUCT
#endif

class Solver;

class SolutionExtender
{
    public:
        SolutionExtender(Solver* _solver, const vector<lbool>& _assigns);
        void extend();
        bool addClause(const vector<Lit>& lits, const Lit blockedOn = lit_Undef);
        void enqueue(const Lit lit);

        lbool value(const Lit lit) const
        {
            return assigns[lit.var()] ^ lit.sign();
        }

        lbool value(const uint32_t var) const
        {
            return assigns[var];
        }

    private:
        void replaceSet(Lit toSet);
        void replaceBackwardSet(const Lit toSet);
        bool propagateCl(const Clause* cl, const Lit blockedOn);
        bool propagate();
        bool prop_bin_cl(
            Watched*& i
            , const Lit p
        );
        bool satisfiedNorm(const vector<Lit>& lits) const;
        bool satisfiedXor(const vector<Lit>& lits, const bool rhs) const;
        Lit pickBranchLit();

        uint32_t nVarsOuter() const
        {
            return assigns.size();
        }

        //To reduce mem alloc overhead
        vector<Lit> tmpLits;


        Solver* solver;
        vector<ClOffset> clausesToFree;
        uint32_t qhead;
        vector<Lit> trail;
        vector<lbool> assigns;
};

} //end namespace

#endif //__SOLUTIONEXTENDER_H__
