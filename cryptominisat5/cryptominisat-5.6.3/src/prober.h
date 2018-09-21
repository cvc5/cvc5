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


#ifndef __PROBER_H__
#define __PROBER_H__

#include <set>
#include <map>
#include <vector>

#include "solvertypes.h"
#include "clause.h"

namespace CMSat {

using std::set;
using std::map;
using std::vector;

class Solver;

//#define DEBUG_REMOVE_USELESS_BIN

class Prober {
    public:
        explicit Prober(Solver* _solver);
        bool probe(vector<uint32_t>* probe_order = NULL);
        int force_stamp = -1; // For testing. 1,2 = DFS (2=irred, 1=red), 0 = BFS, -1 = DONTCARE

        struct Stats
        {
            void clear()
            {
                Stats tmp;
                *this = tmp;
            }

            Stats& operator +=(const Stats& other)
            {
                //Time
                cpu_time += other.cpu_time;
                timeAllocated += other.timeAllocated;
                numCalls += other.numCalls;

                //Probe stats
                numFailed += other.numFailed;
                numProbed += other.numProbed;
                numLoopIters += other.numLoopIters;
                numVarProbed += other.numVarProbed;
                numVisited += other.numVisited;
                zeroDepthAssigns += other.zeroDepthAssigns;

                //Propagation stats
                propStats += other.propStats;
                conflStats += other.conflStats;

                //Binary clause
                addedBin += other.addedBin;
                removedIrredBin += other.removedIrredBin;
                removedRedBin += other.removedRedBin;

                //Compare against
                origNumFreeVars += other.origNumFreeVars;
                origNumBins += other.origNumBins;

                //Bothprop
                bothSameAdded += other.bothSameAdded;

                return *this;
            }

            void print(const size_t nVars, const bool do_print_times) const
            {
                cout << "c -------- PROBE STATS ----------" << endl;
                print_stats_line("c probe time"
                    , cpu_time
                    , ratio_for_stat(timeAllocated, cpu_time*1000.0*1000.0)
                    , "(Mega BP+HP)/s"
                );

                print_stats_line("c called"
                    , numCalls
                    , ratio_for_stat(cpu_time, numCalls)
                    , "s/call"
                );

                int64_t unused_time = ((int64_t)timeAllocated - (int64_t)(propStats.bogoProps + propStats.otfHyperTime));
                print_stats_line("c unused Mega BP+HP"
                    , (double)unused_time/(1000.0*1000.0)
                    , ratio_for_stat(cpu_time, propStats.bogoProps + propStats.otfHyperTime)*(double)unused_time
                    , "est. secs"
                );

                print_stats_line("c 0-depth-assigns"
                    , zeroDepthAssigns
                    , stats_line_percent(zeroDepthAssigns, nVars)
                    , "% vars");

                print_stats_line("c bothsame"
                    , bothSameAdded
                    , stats_line_percent(bothSameAdded, numVisited)
                    , "% visited"
                );

                print_stats_line("c probed"
                    , numProbed
                    , ratio_for_stat(numProbed, cpu_time)
                    , "probe/sec"
                );

                print_stats_line("c loop iters"
                    , numLoopIters
                    , stats_line_percent(numVarProbed, numLoopIters)
                    , "% var probed"
                );

                print_stats_line("c failed"
                    , numFailed
                    , stats_line_percent(numFailed, numProbed)
                    , "% of probes"
                );

                print_stats_line("c visited"
                    , (double)numVisited/(1000.0*1000.0)
                    , "M lits"
                    , stats_line_percent(numVisited, origNumFreeVars*2)
                    , "% of available lits"
                );

                print_stats_line("c bin add"
                    , addedBin
                    , stats_line_percent(addedBin, origNumBins)
                    , "% of bins"
                );

                print_stats_line("c irred bin rem"
                    , removedIrredBin
                    , stats_line_percent(removedIrredBin, origNumBins)
                    , "% of bins"
                );

                print_stats_line("c red bin rem"
                    , removedRedBin
                    , stats_line_percent(removedRedBin, origNumBins)
                    , "% of bins"
                );

                print_stats_line("c time"
                    , cpu_time
                    , "s");

                conflStats.print(cpu_time, do_print_times);
                propStats.print(cpu_time);
                cout << "c -------- PROBE STATS END ----------" << endl;
            }

            void print_short(const Solver* solver, const bool time_out, const double time_remain) const;

            //Time
            double cpu_time = 0;
            uint64_t timeAllocated = 0;
            uint64_t numCalls = 0;

            //Probe stats
            uint64_t numFailed = 0;
            uint64_t numProbed = 0;
            uint64_t numLoopIters = 0;
            uint64_t numVarProbed = 0;
            uint64_t numVisited = 0;
            uint64_t zeroDepthAssigns = 0;

            //Propagation stats
            PropStats propStats;
            ConflStats conflStats;

            //Binary clause
            uint64_t addedBin = 0;
            uint64_t removedIrredBin = 0;
            uint64_t removedRedBin = 0;

            //Compare against
            uint64_t origNumFreeVars = 0;
            uint64_t origNumBins = 0;

            //Bothprop
            uint64_t bothSameAdded = 0;
        };

        const Stats& get_stats() const;
        size_t mem_used() const;

    private:
        //Main
        vector<uint32_t> vars_to_probe;
        bool try_this(const Lit lit, const bool first);
        bool propagate(Lit& failed);
        vector<char> visitedAlready;
        Solver* solver; ///<The solver we are updating&working with
        void checkOTFRatio();
        uint64_t limit_used() const;
        void reset_stats_and_state();
        uint64_t calc_num_props_limit();
        void clean_clauses_before_probe();
        uint64_t update_num_props_limit_based_on_prev_perf(uint64_t num_props_limit);
        void clean_clauses_after_probe();
        void check_if_must_disable_otf_hyperbin_and_tred(const uint64_t num_props_limit);
        void check_if_must_disable_cache_update();
        vector<uint32_t> randomize_possible_choices();
        void update_and_print_stats(const double myTime, const uint64_t num_props_limit);
        bool check_timeout_due_to_hyperbin();

        //For bothprop
        vector<uint32_t> propagatedBitSet;
        vector<bool> propagated; ///<These lits have been propagated by propagating the lit picked
        vector<bool> propValue; ///<The value (0 or 1) of the lits propagated set in "propagated"
        vector<Lit> toEnqueue;
        vector<Lit> tmp_lits;
        void clear_up_before_first_set();

        void update_cache(Lit thisLit, Lit lit, size_t numElemsSet);
        void check_and_set_both_prop(Lit probed_lit, uint32_t var, bool first);
        void add_rest_of_lits_to_cache(Lit lit);

        //For hyper-bin resolution
        #ifdef DEBUG_REMOVE_USELESS_BIN
        void testBinRemoval(const Lit origLit);
        void fillTestUselessBinRemoval(const Lit lit);
        vector<uint32_t> origNLBEnqueuedVars;
        vector<uint32_t> origEnqueuedVars;
        #endif

        //Multi-level
        void calcNegPosDist();
        bool tryMultiLevel(const vector<uint32_t>& vars, uint32_t& enqueued, uint32_t& finished, uint32_t& numFailed);
        bool tryMultiLevelAll();
        void fillToTry(vector<uint32_t>& toTry);

        //Used to count extra time, must be cleared at every startup
        uint64_t extraTime;
        uint64_t extraTimeCache;

        //Stats
        Stats runStats;
        Stats globalStats;

        ///If last time we were successful, do it more
        double numPropsMultiplier;
        ///How successful were we last time?
        uint32_t lastTimeZeroDepthAssings;

        uint64_t single_prop_tout;

};

inline const Prober::Stats& Prober::get_stats() const
{
    return globalStats;
}

} //end namespace;

#endif //__PROBER_H__

