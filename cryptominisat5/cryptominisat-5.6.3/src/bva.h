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

#ifndef __BVA_H__
#define __BVA_H__

#include "heap.h"
#include "watched.h"
#include "clause.h"
#include "touchlist.h"
#include <vector>
using std::vector;

namespace CMSat {

class Solver;
class OccSimplifier;

class BVA
{
public:
    BVA(Solver* _solver, OccSimplifier* _simplifier);
    bool bounded_var_addition();
    size_t mem_used() const;

private:
    Solver* solver;
    OccSimplifier* simplifier;
    vector<uint16_t>& seen;
    vector<uint8_t>& seen2;

    bool bva_verbosity = 0;
    size_t bva_worked;
    size_t bva_simp_size;
    struct lit_pair{
        lit_pair(Lit a, Lit b = lit_Undef)
        {
            if (b == lit_Undef) {
                lit1 = a;
            } else {
                assert(false && "lits are supposed to be sorted in occur lists");
                assert(a != b);
                if (a > b) {
                    std::swap(a, b);
                }
                lit1 = a;
                lit2 = b;
            }
        }

        bool operator==(const lit_pair& other) const
        {
            return lit1 == other.lit1 && lit2 == other.lit2;
        }

        unsigned hash(const uint32_t N) const
        {
            unsigned long h;
            h = lit1.toInt();

            if (lit2 == lit_Undef)
                return h % N;

            h = h*31 + lit2.toInt();
            return h % N;
        }

        bool operator!=(const lit_pair& other) const
        {
            return !(*this == other);
        }

        Lit lit1;
        Lit lit2;
    };
    struct PotentialClause {
        PotentialClause(const lit_pair _lits, const OccurClause cl) :
            lits(_lits)
            , occur_cl(cl)
        {}

        bool operator<(const PotentialClause& other) const
        {
            if (lits == other.lits)
                return false;

            if (lits.lit1 != other.lits.lit1)
                return lits.lit1 < other.lits.lit1;

            return lits.lit2 < other.lits.lit2;
        }

        lit_pair lits;
        OccurClause occur_cl;
        string to_string(const Solver* solver) const;
    };
    struct m_cls_lits_and_red
    {
        //Used during removal to lower overhead
        m_cls_lits_and_red(const vector<Lit>& _lits, bool _red) :
            lits(_lits)
            , red(_red)
        {}
        vector<Lit> lits;
        bool red;
    };
    size_t calc_watch_irred_size(const Lit lit) const;
    void calc_watch_irred_sizes();
    lit_pair most_occuring_lit_in_potential(size_t& num_occur);
    lit_pair lit_diff_watches(const OccurClause& a, const OccurClause& b);
    Lit least_occurring_except(const OccurClause& c);
    bool simplifies_system(const size_t num_occur) const;
    int simplification_size(
        const int m_lit_size
        , const int m_cls_size
    ) const;
    void fill_potential(const Lit lit);
    bool try_bva_on_lit(const Lit lit);
    bool bva_simplify_system();
    void update_touched_lits_in_bva();
    bool add_longer_clause(const Lit lit, const OccurClause& cl);
    void remove_duplicates_from_m_cls();
    void remove_matching_clause(
        const m_cls_lits_and_red& cl_lits
        , const lit_pair lit_replace
    );
    Clause* find_cl_for_bva(
        const vector<Lit>& torem
        , const bool red
    ) const;
    void fill_m_cls_lits_and_red();
    vector<Lit> bva_tmp_lits; //To reduce overhead
    vector<m_cls_lits_and_red> m_cls_lits; //used during removal to lower overhead
    vector<Lit> to_remove; //to reduce overhead
    vector<PotentialClause> potential;
    vector<lit_pair> m_lits;
    vector<lit_pair> m_lits_this_cl;
    vector<OccurClause> m_cls;
    vector<size_t> watch_irred_sizes;
    struct VarBVAOrder
    {
        explicit VarBVAOrder(vector<size_t>& _watch_irred_sizes) :
            watch_irred_sizes(_watch_irred_sizes)
        {}

        bool operator()(const uint32_t lit1_uint, const uint32_t lit2_uint) const;
        vector<size_t>& watch_irred_sizes;
    };
    Heap<VarBVAOrder> var_bva_order;
    TouchList touched;

    int64_t bounded_var_elim_time_limit;
};

}

#endif //__BVA_H__
