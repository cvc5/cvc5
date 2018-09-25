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

#include "solvertypes.h"
#include "watched.h"
#include "watcharray.h"

namespace CMSat {

class SharedData;
class Solver;
class DataSync
{
    public:
        DataSync(Solver* solver, SharedData* sharedData);
        bool enabled();
        void new_var(const bool bva);
        void new_vars(const size_t n);
        bool syncData();
        void save_on_var_memory();
        void rebuild_bva_map();
        void updateVars(
           const vector<uint32_t>& outerToInter
            , const vector<uint32_t>& interToOuter
        );

        template <class T> void signalNewBinClause(T& ps);
        void signalNewBinClause(Lit lit1, Lit lit2);

        struct Stats
        {
            uint32_t sentUnitData = 0;
            uint32_t recvUnitData = 0;
            uint32_t sentBinData = 0;
            uint32_t recvBinData = 0;
        };
        const Stats& get_stats() const;

    private:
        void extend_bins_if_needed();
        Lit map_outside_without_bva(Lit lit) const;
        bool shareUnitData();
        bool syncBinFromOthers();
        bool syncBinFromOthers(const Lit lit, const vector<Lit>& bins, uint32_t& finished, watch_subarray ws);
        void syncBinToOthers();
        void clear_set_binary_values();
        void addOneBinToOthers(const Lit lit1, const Lit lit2);
        bool shareBinData();

        //stuff to sync
        vector<std::pair<Lit, Lit> > newBinClauses;

        //stats
        uint64_t lastSyncConf = 0;
        vector<uint32_t> syncFinish;
        Stats stats;

        //Other systems
        Solver* solver;
        SharedData* sharedData;

        //misc
        vector<uint16_t>& seen;
        vector<Lit>& toClear;
        vector<uint32_t> outer_to_without_bva_map;
        bool must_rebuild_bva_map = false;
};

inline const DataSync::Stats& DataSync::get_stats() const
{
    return stats;
}

template <class T>
inline void DataSync::signalNewBinClause(T& ps)
{
    if (sharedData == NULL) {
        return;
    }
    //assert(ps.size() == 2);
    signalNewBinClause(ps[0], ps[1]);
}

inline Lit DataSync::map_outside_without_bva(const Lit lit) const
{
    return Lit(outer_to_without_bva_map[lit.var()], lit.sign());

}

inline bool DataSync::enabled()
{
    return sharedData != NULL;
}

}
