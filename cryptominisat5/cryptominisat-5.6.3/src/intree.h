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

#include "cloffset.h"
#include "solvertypes.h"
#include "propby.h"

#include <vector>
#include <deque>
using std::vector;
using std::deque;

namespace CMSat {

class Solver;

class InTree
{
public:
    InTree(Solver* _solver);
    bool intree_probe();

    struct QueueElem
    {
        QueueElem(Lit _propagated, Lit _other_lit, bool _red) :
            propagated(_propagated)
            , other_lit(_other_lit)
            , red(_red)
        {}

        Lit propagated;
        Lit other_lit;
        bool red;
    };

    struct ResetReason
    {
        ResetReason(uint32_t _var_reason_changed, PropBy _orig_propby) :
            var_reason_changed(_var_reason_changed)
            , orig_propby(_orig_propby)
        {}

        uint32_t var_reason_changed;
        PropBy orig_propby;
    };

    double mem_used() const;

private:

    bool check_timeout_due_to_hyperbin();
    void unmark_all_bins();
    void randomize_roots();
    bool handle_lit_popped_from_queue(const Lit lit, const Lit propagating, const bool red);
    bool empty_failed_list();
    void fill_roots();
    bool watches_only_contains_nonbin(const Lit lit) const;
    bool replace_until_fixedpoint(bool& aborted);
    void enqueue(const Lit lit, const Lit other_lit, bool red_cl);

    void setup();
    void build_intree();
    void do_one();
    void tree_look();

    vector<Lit> roots;
    vector<Lit> failed;
    vector<ResetReason> reset_reason_stack;
    deque<QueueElem> queue;
    vector<char> depth_failed;
    int64_t bogoprops_to_use;
    int64_t bogoprops_remain;

    size_t hyperbin_added;
    size_t removedIrredBin;
    size_t removedRedBin;
    size_t numCalls = 0;

    Solver* solver;
    vector<uint16_t>& seen;
};

inline std::ostream& operator<<(std::ostream& os, const InTree::QueueElem& elem)
{
    if (elem.propagated == lit_Undef) {
        os << "NONE";
    } else {
        os << "prop:" << elem.propagated
        << " other_lit:" << elem.other_lit
        << " red: " << elem.red;
    }

    return os;
}

}

