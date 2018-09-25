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

#ifndef SOLVE_FEATURES_H_
#define SOLVE_FEATURES_H_

#include <limits>
#include <cstdint>
#include <string>

namespace CMSat {

struct SolveFeatures
{
    void print_stats() const;

    //Some parameter
    double eps = 0.00001;

    int numVars;
    int numClauses;
    double var_cl_ratio;

    //Clause distribution
    double binary = 0;
    double horn = 0;
    double horn_mean = 0;
    double horn_std = 0;
    double horn_min = std::numeric_limits<double>::max();
    double horn_max = std::numeric_limits<double>::min();
    double horn_spread;

    double vcg_var_mean = 0;
    double vcg_var_std = 0;
    double vcg_var_min = std::numeric_limits<double>::max();
    double vcg_var_max = std::numeric_limits<double>::min();
    double vcg_var_spread;

    double vcg_cls_mean = 0;
    double vcg_cls_std = 0;
    double vcg_cls_min = std::numeric_limits<double>::max();
    double vcg_cls_max = std::numeric_limits<double>::min();
    double vcg_cls_spread;

    double pnr_var_mean = 0;
    double pnr_var_std = 0;
    double pnr_var_min = std::numeric_limits<double>::max();
    double pnr_var_max = std::numeric_limits<double>::min();
    double pnr_var_spread;

    double pnr_cls_mean = 0;
    double pnr_cls_std = 0;
    double pnr_cls_min = std::numeric_limits<double>::max();
    double pnr_cls_max = std::numeric_limits<double>::min();
    double pnr_cls_spread;

    //Conflict clauses
    double avg_confl_size = 0.0;
    double confl_size_min = 0.0;
    double confl_size_max = 0.0;
    double avg_confl_glue = 0.0;
    double confl_glue_min = 0.0;
    double confl_glue_max = 0.0;
    double avg_num_resolutions = 0.0;
    double num_resolutions_min = 0.0;
    double num_resolutions_max = 0.0;
    double learnt_bins_per_confl = 0;

    //Search
    double avg_branch_depth = 0.0;
    double branch_depth_min = 0.0;
    double branch_depth_max = 0.0;
    double avg_trail_depth_delta = 0.0;
    double trail_depth_delta_min = 0.0;
    double trail_depth_delta_max = 0.0;
    double avg_branch_depth_delta = 0.0;
    double props_per_confl = 0.0;
    double confl_per_restart = 0.0;
    double decisions_per_conflict = 0.0;

    //learnt distributions
    struct Distrib {
        double glue_distr_mean = 0;
        double glue_distr_var = 0;
        double size_distr_mean = 0;
        double size_distr_var = 0;
        double activity_distr_mean = 0;
        double activity_distr_var = 0;

        void print(const std::string& pre_print) const;
    };
    Distrib irred_cl_distrib;
    Distrib red_cl_distrib;

    //High-level features
    uint64_t num_gates_found_last;
    uint64_t num_xors_found_last;
};

}

#endif //SOLVE_FEATURES_H_
