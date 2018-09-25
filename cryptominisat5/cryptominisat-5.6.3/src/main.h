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

#ifndef MAIN_H
#define MAIN_H

#include <string>
#include <vector>
#include <memory>
#include <fstream>

#include "solverconf.h"
#include "cryptominisat5/cryptominisat.h"

using std::string;
using std::vector;

#include <boost/program_options.hpp>
namespace po = boost::program_options;
using namespace CMSat;

class Main
{
    public:
        Main(int argc, char** argv);
        ~Main()
        {
            if (dratf) {
                *dratf << std::flush;
                if (dratf != &std::cout) {
                    delete dratf;
                }
            }

            delete solver;
        }

        void parseCommandLine();
        virtual int solve();
        SolverConf conf;

    private:
        //arguments
        int argc;
        char** argv;
        string var_elim_strategy;
        string dratfilname;
        void check_options_correctness();
        void manually_parse_some_options();
        void handle_drat_option();
        void parse_restart_type();
        void parse_polarity_type();
        void check_num_threads_sanity(const unsigned thread_num) const;

        po::positional_options_description p;
        po::options_description all_options;

    protected:
        //Options
        po::variables_map vm;
        virtual void add_supported_options();
        virtual void call_after_parse() {}

        po::options_description help_options_simple;
        po::options_description help_options_complicated;
        po::options_description hiddenOptions;
        po::options_description generalOptions = po::options_description("Main options");

        SATSolver* solver = NULL;

        //File reading
        void readInAFile(SATSolver* solver2, const string& filename);
        void readInStandardInput(SATSolver* solver2);
        void parseInAllFiles(SATSolver* solver2);

        //Helper functions
        void printResultFunc(
            std::ostream* os
            , const bool toFile
            , const lbool ret
        );
        void printVersionInfo();
        int correctReturnValue(const lbool ret) const;
        lbool multi_solutions();
        void dump_red_file();

        //Config
        bool zero_exit_status = false;
        std::string resultFilename;
        std::string debugLib;
        int printResult = true;
        string commandLine;
        unsigned num_threads = 1;
        uint32_t max_nr_of_solutions = 1;
        int sql = 0;
        string sqlite_filename;
        vector<uint32_t> independent_vars;
        std::string independent_vars_str = "";
        bool only_indep_solution = false;

        //Files to read & write
        bool fileNamePresent;
        vector<string> filesToRead;
        std::ofstream* resultfile = NULL;
        string dump_red_fname;
        uint32_t dump_red_max_len = 10000;
        uint32_t dump_red_max_glue = 1000;

        //Drat checker
        std::ostream* dratf = NULL;
        bool dratDebug = false;
        bool clause_ID_needed = false;
};

#endif //MAIN_H
