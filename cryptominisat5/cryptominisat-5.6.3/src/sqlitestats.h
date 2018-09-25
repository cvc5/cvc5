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

#include "sqlstats.h"
#include "solvefeatures.h"
#include <sqlite3.h>

namespace CMSat {


class SQLiteStats: public SQLStats
{
public:
    ~SQLiteStats() override;
    explicit SQLiteStats(std::string _filename) :
        filename(_filename)
    {
    }

    void restart(
        const std::string& restart_type
        , const PropStats& thisPropStats
        , const SearchStats& thisStats
        , const Solver* solver
        , const Searcher* searcher
    ) override;

    void reduceDB(
        const Solver* solver
        , const bool locked
        , const Clause* cl
    ) override;

    void time_passed(
        const Solver* solver
        , const string& name
        , double time_passed
        , bool time_out
        , double percent_time_remain
    ) override;

    void time_passed_min(
        const Solver* solver
        , const string& name
        , double time_passed
    ) override;


    void features(
        const Solver* solver
        , const Searcher* search
        , const SolveFeatures& feat
    ) override;

    void mem_used(
        const Solver* solver
        , const string& name
        , double given_time
        , uint64_t mem_used_mb
    ) override;

    void dump_clause_stats(
        const Solver* solver
        , uint64_t clauseID
        , uint32_t glue
        , const uint32_t backtrack_level
        , uint32_t size
        , AtecedentData<uint16_t> resoltypes
        , size_t decision_level
        , size_t trail_depth
        , uint64_t conflicts_this_restart
        , const std::string& rest_type
        , const SearchHist& hist
        , const double last_dec_var_act_0
        , const double last_dec_var_act_1
        , const double first_dec_var_act_0
        , const double first_dec_var_act_1
    ) override;

    bool setup(const Solver* solver) override;
    void finishup(lbool status) override;
    void add_tag(const std::pair<std::string, std::string>& tag) override;

private:

    bool connectServer(const int verbosity);
    void getID(const Solver* solver);
    bool tryIDInSQL(const Solver* solver);

    void addStartupData();
    void initRestartSTMT();
    void initTimePassedSTMT();
    void initMemUsedSTMT();
    void init_clause_stats_STMT();
    void init_features();

    void writeQuestionMarks(size_t num, std::stringstream& ss);
    void initReduceDBSTMT();

    sqlite3_stmt *stmtTimePassed = NULL;
    sqlite3_stmt *stmtMemUsed = NULL;
    sqlite3_stmt *stmtReduceDB = NULL;
    sqlite3_stmt *stmtRst = NULL;
    sqlite3_stmt *stmtFeat = NULL;
    sqlite3_stmt *stmt_clause_stats = NULL;

    sqlite3 *db = NULL;
    bool setup_ok = false;
    const string filename;
};

}
