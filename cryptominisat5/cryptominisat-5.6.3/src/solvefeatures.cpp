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

#include "solvefeatures.h"
#include <iostream>
using std::string;
using std::cout;
using std::endl;

using namespace CMSat;


void SolveFeatures::print_stats() const
{
    cout << "c [features] ";
    cout << "numVars " << numVars << ", ";
    cout << "numClauses " << numClauses << ", ";
    cout << "var_cl_ratio " << var_cl_ratio << ", ";


    //Clause distribution
    cout << "binary " << binary << ", ";

    cout << "horn " << horn << ", ";
    cout << "horn_mean " << horn_mean << ", ";
    cout << "horn_std " << horn_std << ", ";
    cout << "horn_min " << horn_min << ", ";
    cout << "horn_max " << horn_max << ", ";
    cout << "horn_spread " << horn_spread << ", ";

    cout << "vcg_var_mean " << vcg_var_mean << ", ";
    cout << "vcg_var_std " << vcg_var_std << ", ";
    cout << "vcg_var_min " << vcg_var_min << ", ";
    cout << "vcg_var_max " << vcg_var_max << ", ";
    cout << "vcg_var_spread " << vcg_var_spread << ", ";

    cout << "vcg_cls_mean " << vcg_cls_mean << ", ";
    cout << "vcg_cls_std " << vcg_cls_std << ", ";
    cout << "vcg_cls_min " << vcg_cls_min << ", ";
    cout << "vcg_cls_max " << vcg_cls_max << ", ";
    cout << "vcg_cls_spread " << vcg_cls_spread << ", ";

    cout << "pnr_var_mean " << pnr_var_mean << ", ";
    cout << "pnr_var_std " << pnr_var_std << ", ";
    cout << "pnr_var_min " << pnr_var_min << ", ";
    cout << "pnr_var_max " << pnr_var_max << ", ";
    cout << "pnr_var_spread " << pnr_var_spread << ", ";

    cout << "pnr_cls_mean " << pnr_cls_mean << ", ";
    cout << "pnr_cls_std " << pnr_cls_std << ", ";
    cout << "pnr_cls_min " << pnr_cls_min << ", ";
    cout << "pnr_cls_max " << pnr_cls_max << ", ";
    cout << "pnr_cls_spread " << pnr_cls_spread << ", ";

    //Conflicts
    cout << "avg_confl_size " << avg_confl_size << ", ";
    cout << "confl_size_min " << confl_size_min << ", ";
    cout << "confl_size_max " << confl_size_max << ", ";
    cout << "avg_confl_glue " << avg_confl_glue << ", ";
    cout << "confl_glue_min " << confl_glue_min << ", ";
    cout << "confl_glue_max " << confl_glue_max << ", ";
    cout << "avg_num_resolutions " << avg_num_resolutions << ", ";
    cout << "num_resolutions_min " << num_resolutions_min << ", ";
    cout << "num_resolutions_max " << num_resolutions_max << ", ";
    cout << "learnt_bins_per_confl " << learnt_bins_per_confl << ", ";

    //Search
    cout << "avg_branch_depth " << avg_branch_depth << ", ";
    cout << "branch_depth_min " << branch_depth_min << ", ";
    cout << "branch_depth_max " << branch_depth_max << ", ";
    cout << "avg_trail_depth_delta " << avg_trail_depth_delta << ", ";
    cout << "trail_depth_delta_min " << trail_depth_delta_min << ", ";
    cout << "trail_depth_delta_max " << trail_depth_delta_max << ", ";
    cout << "avg_branch_depth_delta " << avg_branch_depth_delta << ", ";
    cout << "props_per_confl " << props_per_confl << ", ";
    cout << "confl_per_restart " << confl_per_restart << ", ";
    cout << "decisions_per_conflict " << decisions_per_conflict << ", ";

    //distributions
    irred_cl_distrib.print("irred_cl_distrib.");
    red_cl_distrib.print("red_cl_distrib.");

    cout << "num_gates_found_last " << num_gates_found_last << ", ";
    cout << "num_xors_found_last " << num_xors_found_last;
    cout << endl;
}

void SolveFeatures::Distrib::print(const string& pre_print) const
{
    cout << pre_print <<"glue_distr_mean " << glue_distr_mean << ", ";
    cout << pre_print <<"glue_distr_var " << glue_distr_var << ", ";
    cout << pre_print <<"size_distr_mean " << size_distr_mean << ", ";
    cout << pre_print <<"size_distr_var " << size_distr_var << ", ";
    cout << pre_print <<"uip_use_distr_mean " << 0 << ", ";
    cout << pre_print <<"uip_use_distr_var " << 0 << ", ";
    cout << pre_print <<"activity_distr_mean " << activity_distr_mean << ", ";
    cout << pre_print <<"activity_distr_var " << activity_distr_var << ", ";
}
