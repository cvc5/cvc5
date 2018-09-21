#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2017  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

from __future__ import print_function
import sqlite3
import optparse
import time
import pickle
import re
import pandas as pd
import numpy as np
import os.path

from sklearn.model_selection import train_test_split
import sklearn.tree
import sklearn.svm
import sklearn.ensemble
import sklearn.metrics
from sklearn.preprocessing import LabelEncoder


##############
# HOW TO GET A NICE LIST
##############
# go into .stdout.gz outputs:
# zgrep "s UNSAT" * | cut -d ":" -f 1 > ../candidate_files_large_fixed_adjust_guess-12-April
#
# --> edit file to have the format:
# zgrep -H "Total" large_hybr-12-April-2016-VAGTY-e4119a1b0-tout-1500-mout-1600/1dlx_c_iq57_a.cnf.gz.stdout.gz
#
# run:
# ./candidate_files_large_hybr-12-April-2016-VAGTY.sh | awk '{if ($5 < 600 && $5 > 200) print $1 " -- " $5}' | cut -d "/" -f 2 | cut -d ":" -f 1 | sed "s/.stdout.*//" > ../unsat_small_candidates2.txt


################
# EXAMPLE TO RUN THIS AGAINST
################
# 6s153.cnf.gz

class QueryHelper:
    def __init__(self, dbfname):
        if not os.path.isfile(dbfname):
            print("ERROR: Database file '%s' does not exist" % dbfname)
            exit(-1)

        self.conn = sqlite3.connect(dbfname)
        self.c = self.conn.cursor()
        self.runID = self.find_runID()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.conn.commit()
        self.conn.close()

    def find_runID(self):
        q = """
        SELECT runID
        FROM startUp
        order by startTime desc
        limit 1
        """

        runID = None
        for row in self.c.execute(q):
            if runID is not None:
                print("ERROR: More than one RUN IDs in file!")
                exit(-1)
            runID = int(row[0])

        print("runID: %d" % runID)
        return runID


class Query2 (QueryHelper):
    def create_indexes(self):
        print("Recreating indexes...")
        t = time.time()
        q = """
        drop index if exists `idxclid`;
        drop index if exists `idxclid2`;
        drop index if exists `idxclid3`;
        drop index if exists `idxclid4`;
        drop index if exists `idxclid5`;
        drop index if exists `idxclid6`;

        create index `idxclid` on `clauseStats` (`runID`,`clauseID`);
        create index `idxclid2` on `clauseStats` (`runID`,`prev_restart`);
        create index `idxclid3` on `goodClauses` (`runID`,`clauseID`);
        create index `idxclid4` on `restart` (`runID`, `restarts`);
        create index `idxclid5` on `tags` (`runID`, `tagname`);
        create index `idxclid6` on `reduceDB` (`runID`,`clauseID`, `dump_no`);
        """
        for l in q.split('\n'):
            self.c.execute(l)

        print("indexes created T: %-3.2f s" % (time.time() - t))

    def get_clstats(self):

        # partially done with tablestruct_sql and SED: sed -e 's/`\(.*\)`.*/rst.`\1` as `rst.\1`/' ../tmp.txt
        restart_dat = """
        -- , rst.`runID` as `rst.runID`
        -- , rst.`simplifications` as `rst.simplifications`
        -- , rst.`restarts` as `rst.restarts`
        -- , rst.`conflicts` as `rst.conflicts`
        -- , rst.`latest_feature_calc` as `rst.latest_feature_calc`
        -- rst.`runtime` as `rst.runtime`
        , rst.`numIrredBins` as `rst.numIrredBins`
        , rst.`numIrredLongs` as `rst.numIrredLongs`
        , rst.`numRedBins` as `rst.numRedBins`
        , rst.`numRedLongs` as `rst.numRedLongs`
        , rst.`numIrredLits` as `rst.numIrredLits`
        , rst.`numredLits` as `rst.numredLits`
        , rst.`glue` as `rst.glue`
        , rst.`glueSD` as `rst.glueSD`
        , rst.`glueMin` as `rst.glueMin`
        , rst.`glueMax` as `rst.glueMax`
        , rst.`size` as `rst.size`
        , rst.`sizeSD` as `rst.sizeSD`
        , rst.`sizeMin` as `rst.sizeMin`
        , rst.`sizeMax` as `rst.sizeMax`
        , rst.`resolutions` as `rst.resolutions`
        , rst.`resolutionsSD` as `rst.resolutionsSD`
        , rst.`resolutionsMin` as `rst.resolutionsMin`
        , rst.`resolutionsMax` as `rst.resolutionsMax`
        , rst.`branchDepth` as `rst.branchDepth`
        , rst.`branchDepthSD` as `rst.branchDepthSD`
        , rst.`branchDepthMin` as `rst.branchDepthMin`
        , rst.`branchDepthMax` as `rst.branchDepthMax`
        , rst.`branchDepthDelta` as `rst.branchDepthDelta`
        , rst.`branchDepthDeltaSD` as `rst.branchDepthDeltaSD`
        , rst.`branchDepthDeltaMin` as `rst.branchDepthDeltaMin`
        , rst.`branchDepthDeltaMax` as `rst.branchDepthDeltaMax`
        , rst.`trailDepth` as `rst.trailDepth`
        , rst.`trailDepthSD` as `rst.trailDepthSD`
        , rst.`trailDepthMin` as `rst.trailDepthMin`
        , rst.`trailDepthMax` as `rst.trailDepthMax`
        , rst.`trailDepthDelta` as `rst.trailDepthDelta`
        , rst.`trailDepthDeltaSD` as `rst.trailDepthDeltaSD`
        , rst.`trailDepthDeltaMin` as `rst.trailDepthDeltaMin`
        , rst.`trailDepthDeltaMax` as `rst.trailDepthDeltaMax`
        , rst.`propBinIrred` as `rst.propBinIrred`
        , rst.`propBinRed` as `rst.propBinRed`
        , rst.`propLongIrred` as `rst.propLongIrred`
        , rst.`propLongRed` as `rst.propLongRed`
        , rst.`conflBinIrred` as `rst.conflBinIrred`
        , rst.`conflBinRed` as `rst.conflBinRed`
        , rst.`conflLongIrred` as `rst.conflLongIrred`
        , rst.`conflLongRed` as `rst.conflLongRed`
        , rst.`learntUnits` as `rst.learntUnits`
        , rst.`learntBins` as `rst.learntBins`
        , rst.`learntLongs` as `rst.learntLongs`
        , rst.`resolBinIrred` as `rst.resolBinIrred`
        , rst.`resolBinRed` as `rst.resolBinRed`
        , rst.`resolLIrred` as `rst.resolLIrred`
        , rst.`resolLRed` as `rst.resolLRed`
        -- , rst.`propagations` as `rst.propagations`
        -- , rst.`decisions` as `rst.decisions`
        -- , rst.`flipped` as `rst.flipped`
        , rst.`varSetPos` as `rst.varSetPos`
        , rst.`varSetNeg` as `rst.varSetNeg`
        , rst.`free` as `rst.free`
        -- , rst.`replaced` as `rst.replaced`
        -- , rst.`eliminated` as `rst.eliminated`
        -- , rst.`set` as `rst.set`
        -- , rst.`clauseIDstartInclusive` as `rst.clauseIDstartInclusive`
        -- , rst.`clauseIDendExclusive` as `rst.clauseIDendExclusive`
        """

        rdb0_dat = """
        -- , rdb0.`runID` as `rdb0.runID`
        -- , rdb0.`simplifications` as `rdb0.simplifications`
        -- , rdb0.`restarts` as `rdb0.restarts`
        , rdb0.`conflicts` as `rdb0.conflicts`
        -- , rdb0.`runtime` as `rdb0.runtime`

        -- , rdb0.`clauseID` as `rdb0.clauseID`
        , rdb0.`dump_no` as `rdb0.dump_no`
        , rdb0.`conflicts_made` as `rdb0.conflicts_made`
        , rdb0.`sum_of_branch_depth_conflict` as `rdb0.sum_of_branch_depth_conflict`
        , rdb0.`propagations_made` as `rdb0.propagations_made`
        , rdb0.`clause_looked_at` as `rdb0.clause_looked_at`
        , rdb0.`used_for_uip_creation` as `rdb0.used_for_uip_creation`
        , rdb0.`last_touched_diff` as `rdb0.last_touched_diff`
        , rdb0.`activity_rel` as `rdb0.activity_rel`
        , rdb0.`locked` as `rdb0.locked`
        , rdb0.`in_xor` as `rdb0.in_xor`
        -- , rdb0.`glue` as `rdb0.glue`
        -- , rdb0.`size` as `rdb0.size`
        , rdb0.`ttl` as `rdb0.ttl`
        """

        clause_dat = """
        -- , cl.`runID` as `cl.runID`
        -- , cl.`simplifications` as `cl.simplifications`
        -- , cl.`restarts` as `cl.restarts`
        -- , cl.`prev_restart` as `cl.prev_restart`
        -- , cl.`conflicts` as `cl.conflicts`
        -- , cl.`latest_feature_calc` as `cl.latest_feature_calc`
        -- , cl.`clauseID` as `cl.clauseID`
        , cl.`glue` as `cl.glue`
        , cl.`size` as `cl.size`
        , cl.`conflicts_this_restart` as `cl.conflicts_this_restart`
        , cl.`num_overlap_literals` as `cl.num_overlap_literals`
        , cl.`num_antecedents` as `cl.num_antecedents`
        , cl.`num_total_lits_antecedents` as `cl.num_total_lits_antecedents`
        , cl.`antecedents_avg_size` as `cl.antecedents_avg_size`
        , cl.`backtrack_level` as `cl.backtrack_level`
        , cl.`decision_level` as `cl.decision_level`
        , cl.`decision_level_pre1` as `cl.decision_level_pre1`
        , cl.`decision_level_pre2` as `cl.decision_level_pre2`
        , cl.`trail_depth_level` as `cl.trail_depth_level`
        , cl.`cur_restart_type` as `cl.cur_restart_type`
        , cl.`atedecents_binIrred` as `cl.atedecents_binIrred`
        , cl.`atedecents_binRed` as `cl.atedecents_binRed`
        , cl.`atedecents_longIrred` as `cl.atedecents_longIrred`
        , cl.`atedecents_longRed` as `cl.atedecents_longRed`
        -- , cl.`vsids_vars_avg` as `cl.vsids_vars_avg`
        -- , cl.`vsids_vars_var` as `cl.vsids_vars_var`
        -- , cl.`vsids_vars_min` as `cl.vsids_vars_min`
        -- , cl.`vsids_vars_max` as `cl.vsids_vars_max`
        , cl.`antecedents_glue_long_reds_avg` as `cl.antecedents_glue_long_reds_avg`
        , cl.`antecedents_glue_long_reds_var` as `cl.antecedents_glue_long_reds_var`
        , cl.`antecedents_glue_long_reds_min` as `cl.antecedents_glue_long_reds_min`
        , cl.`antecedents_glue_long_reds_max` as `cl.antecedents_glue_long_reds_max`
        , cl.`antecedents_long_red_age_avg` as `cl.antecedents_long_red_age_avg`
        , cl.`antecedents_long_red_age_var` as `cl.antecedents_long_red_age_var`
        , cl.`antecedents_long_red_age_min` as `cl.antecedents_long_red_age_min`
        , cl.`antecedents_long_red_age_max` as `cl.antecedents_long_red_age_max`
        -- , cl.`vsids_of_resolving_literals_avg` as `cl.vsids_of_resolving_literals_avg`
        -- , cl.`vsids_of_resolving_literals_var` as `cl.vsids_of_resolving_literals_var`
        -- , cl.`vsids_of_resolving_literals_min` as `cl.vsids_of_resolving_literals_min`
        -- , cl.`vsids_of_resolving_literals_max` as `cl.vsids_of_resolving_literals_max`
        -- , cl.`vsids_of_all_incoming_lits_avg` as `cl.vsids_of_all_incoming_lits_avg`
        -- , cl.`vsids_of_all_incoming_lits_var` as `cl.vsids_of_all_incoming_lits_var`
        -- , cl.`vsids_of_all_incoming_lits_min` as `cl.vsids_of_all_incoming_lits_min`
        -- , cl.`vsids_of_all_incoming_lits_max` as `cl.vsids_of_all_incoming_lits_max`
        -- , cl.`antecedents_antecedents_vsids_avg` as `cl.antecedents_antecedents_vsids_avg`
        , cl.`decision_level_hist` as `cl.decision_level_hist`
        , cl.`backtrack_level_hist_lt` as `cl.backtrack_level_hist_lt`
        , cl.`trail_depth_level_hist` as `cl.trail_depth_level_hist`
        -- , cl.`vsids_vars_hist` as `cl.vsids_vars_hist`
        , cl.`size_hist` as `cl.size_hist`
        , cl.`glue_hist` as `cl.glue_hist`
        , cl.`num_antecedents_hist` as `cl.num_antecedents_hist`
        , cl.`antec_sum_size_hist` as `cl.antec_sum_size_hist`
        , cl.`antec_overlap_hist` as `cl.antec_overlap_hist`

        , cl.`branch_depth_hist_queue` as `cl.branch_depth_hist_queue`
        , cl.`trail_depth_hist` as `cl.trail_depth_hist`
        , cl.`trail_depth_hist_longer` as `cl.trail_depth_hist_longer`
        , cl.`num_resolutions_hist` as `cl.num_resolutions_hist`
        , cl.`confl_size_hist` as `cl.confl_size_hist`
        , cl.`trail_depth_delta_hist` as `cl.trail_depth_delta_hist`
        , cl.`backtrack_level_hist` as `cl.backtrack_level_hist`
        , cl.`glue_hist_queue` as `cl.glue_hist_queue`
        , cl.`glue_hist_long` as `cl.glue_hist_long`
        """

        feat_dat = """
        -- , feat.`simplifications` as `feat.simplifications`
        -- , feat.`restarts` as `feat.restarts`
        , feat.`conflicts` as `feat.conflicts`
        -- , feat.`latest_feature_calc` as `feat.latest_feature_calc`
        , feat.`numVars` as `feat.numVars`
        , feat.`numClauses` as `feat.numClauses`
        , feat.`var_cl_ratio` as `feat.var_cl_ratio`
        , feat.`binary` as `feat.binary`
        , feat.`horn` as `feat.horn`
        , feat.`horn_mean` as `feat.horn_mean`
        , feat.`horn_std` as `feat.horn_std`
        , feat.`horn_min` as `feat.horn_min`
        , feat.`horn_max` as `feat.horn_max`
        , feat.`horn_spread` as `feat.horn_spread`
        , feat.`vcg_var_mean` as `feat.vcg_var_mean`
        , feat.`vcg_var_std` as `feat.vcg_var_std`
        , feat.`vcg_var_min` as `feat.vcg_var_min`
        , feat.`vcg_var_max` as `feat.vcg_var_max`
        , feat.`vcg_var_spread` as `feat.vcg_var_spread`
        , feat.`vcg_cls_mean` as `feat.vcg_cls_mean`
        , feat.`vcg_cls_std` as `feat.vcg_cls_std`
        , feat.`vcg_cls_min` as `feat.vcg_cls_min`
        , feat.`vcg_cls_max` as `feat.vcg_cls_max`
        , feat.`vcg_cls_spread` as `feat.vcg_cls_spread`
        , feat.`pnr_var_mean` as `feat.pnr_var_mean`
        , feat.`pnr_var_std` as `feat.pnr_var_std`
        , feat.`pnr_var_min` as `feat.pnr_var_min`
        , feat.`pnr_var_max` as `feat.pnr_var_max`
        , feat.`pnr_var_spread` as `feat.pnr_var_spread`
        , feat.`pnr_cls_mean` as `feat.pnr_cls_mean`
        , feat.`pnr_cls_std` as `feat.pnr_cls_std`
        , feat.`pnr_cls_min` as `feat.pnr_cls_min`
        , feat.`pnr_cls_max` as `feat.pnr_cls_max`
        , feat.`pnr_cls_spread` as `feat.pnr_cls_spread`
        , feat.`avg_confl_size` as `feat.avg_confl_size`
        , feat.`confl_size_min` as `feat.confl_size_min`
        , feat.`confl_size_max` as `feat.confl_size_max`
        , feat.`avg_confl_glue` as `feat.avg_confl_glue`
        , feat.`confl_glue_min` as `feat.confl_glue_min`
        , feat.`confl_glue_max` as `feat.confl_glue_max`
        , feat.`avg_num_resolutions` as `feat.avg_num_resolutions`
        , feat.`num_resolutions_min` as `feat.num_resolutions_min`
        , feat.`num_resolutions_max` as `feat.num_resolutions_max`
        , feat.`learnt_bins_per_confl` as `feat.learnt_bins_per_confl`
        , feat.`avg_branch_depth` as `feat.avg_branch_depth`
        , feat.`branch_depth_min` as `feat.branch_depth_min`
        , feat.`branch_depth_max` as `feat.branch_depth_max`
        , feat.`avg_trail_depth_delta` as `feat.avg_trail_depth_delta`
        , feat.`trail_depth_delta_min` as `feat.trail_depth_delta_min`
        , feat.`trail_depth_delta_max` as `feat.trail_depth_delta_max`
        , feat.`avg_branch_depth_delta` as `feat.avg_branch_depth_delta`
        , feat.`props_per_confl` as `feat.props_per_confl`
        , feat.`confl_per_restart` as `feat.confl_per_restart`
        , feat.`decisions_per_conflict` as `feat.decisions_per_conflict`
        , feat.`red_glue_distr_mean` as `feat.red_glue_distr_mean`
        , feat.`red_glue_distr_var` as `feat.red_glue_distr_var`
        , feat.`red_size_distr_mean` as `feat.red_size_distr_mean`
        , feat.`red_size_distr_var` as `feat.red_size_distr_var`
        -- , feat.`red_activity_distr_mean` as `feat.red_activity_distr_mean`
        -- , feat.`red_activity_distr_var` as `feat.red_activity_distr_var`
        -- , feat.`irred_glue_distr_mean` as `feat.irred_glue_distr_mean`
        -- , feat.`irred_glue_distr_var` as `feat.irred_glue_distr_var`
        , feat.`irred_size_distr_mean` as `feat.irred_size_distr_mean`
        , feat.`irred_size_distr_var` as `feat.irred_size_distr_var`
        -- , feat.`irred_activity_distr_mean` as `feat.irred_activity_distr_mean`
        -- , feat.`irred_activity_distr_var` as `feat.irred_activity_distr_var`
        """

        common_restrictions = """
        and cl.restarts > 1 -- to avoid history being invalid
        and cl.runID = {runid}
        and feat.runID = {runid}
        and feat.latest_feature_calc = cl.latest_feature_calc
        and rst.restarts = cl.prev_restart
        and rst.runID = {runid}
        and tags.tagname = "filename"
        and tags.runID = {runid}
        and cl.conflicts > {start_confl}
        """

        common_limits = """
        order by random()
        limit {limit}
        """

        q_count = "SELECT count(*)"
        q_ok_select = """
        SELECT
        tags.tag as "fname"
        {clause_dat}
        {clause2_dat}
        {clause3_dat}
        {restart_dat}
        {feat_dat}
        {rdb0_dat}
        {rdb1_dat}
        {rdb2_dat}
        {rdb3_dat}
        {rdb4_dat}
        , goodcl.num_used as `x.num_used`
        , goodcl.last_confl_used-cl.`conflicts` as `x.lifetime`
        , "OK" as `x.class`
        """

        q_ok = """
        FROM
        clauseStats as cl
        , clauseStats as cl2
        , clauseStats as cl3
        , goodClauses as goodcl
        , restart as rst
        , features as feat
        , reduceDB as rdb0
        , reduceDB as rdb1
        , reduceDB as rdb2
        , reduceDB as rdb3
        , reduceDB as rdb4
        , tags
        WHERE

        cl.clauseID = goodcl.clauseID
        and cl.clauseID != 0
        and cl.runID = goodcl.runID
        and rdb0.runID = cl.runID
        and rdb0.clauseID = cl.clauseID
        and rdb0.dump_no = 0
        and rdb1.runID = cl.runID
        and rdb1.clauseID = cl.clauseID
        and rdb1.dump_no = 1
        and rdb2.runID = cl.runID
        and rdb2.clauseID = cl.clauseID
        and rdb2.dump_no = 2
        and rdb3.runID = cl.runID
        and rdb3.clauseID = cl.clauseID
        and rdb3.dump_no = 3
        and rdb4.runID = cl.runID
        and rdb4.clauseID = cl.clauseID
        and rdb4.dump_no = 4
        and cl2.runID = cl.runID
        and cl2.clauseID = cl.clauseID
        and cl3.runID = cl.runID
        and cl3.clauseID = cl.clauseID
        """
        q_ok += common_restrictions

        # BAD caluses
        q_bad_select = """
        SELECT
        tags.tag as "fname"
        {clause_dat}
        {clause2_dat}
        {clause3_dat}
        {restart_dat}
        {feat_dat}
        {rdb0_dat}
        {rdb1_dat}
        {rdb2_dat}
        {rdb3_dat}
        {rdb4_dat}
        , 0 as `x.num_used`
        , 0 as `x.lifetime`
        , "BAD" as `x.class`
        """

        q_bad = """
        FROM clauseStats as cl left join goodClauses as goodcl
        on cl.clauseID = goodcl.clauseID
        and cl.runID = goodcl.runID
        , clauseStats as cl2
        , clauseStats as cl3
        , restart as rst
        , features as feat
        , reduceDB as rdb0
        , reduceDB as rdb1
        , reduceDB as rdb2
        , reduceDB as rdb3
        , reduceDB as rdb4
        , tags
        WHERE

        goodcl.clauseID is NULL
        and goodcl.runID is NULL
        and cl.clauseID != 0
        and rdb0.runID = cl.runID
        and rdb0.clauseID = cl.clauseID
        and rdb0.dump_no = 0
        and rdb1.runID = cl.runID
        and rdb1.clauseID = cl.clauseID
        and rdb1.dump_no = 1
        and rdb2.runID = cl.runID
        and rdb2.clauseID = cl.clauseID
        and rdb2.dump_no = 2
        and rdb3.runID = cl.runID
        and rdb3.clauseID = cl.clauseID
        and rdb3.dump_no = 3
        and rdb4.runID = cl.runID
        and rdb4.clauseID = cl.clauseID
        and rdb4.dump_no = 4
        and cl2.runID = cl.runID
        and cl2.clauseID = cl.clauseID
        and cl3.runID = cl.runID
        and cl3.clauseID = cl.clauseID
        """
        q_bad += common_restrictions

        myformat = {"runid": self.runID,
                    "limit": 1000*1000*1000,
                    "restart_dat": restart_dat,
                    "clause_dat": clause_dat,
                    "clause2_dat": clause_dat.replace("cl.", "cl2."),
                    "clause3_dat": clause_dat.replace("cl.", "cl3."),
                    "feat_dat": feat_dat,
                    "rdb0_dat": rdb0_dat,
                    "rdb1_dat": rdb0_dat.replace("rdb0.", "rdb1."),
                    "rdb2_dat": rdb0_dat.replace("rdb0.", "rdb2."),
                    "rdb3_dat": rdb0_dat.replace("rdb0.", "rdb3."),
                    "rdb4_dat": rdb0_dat.replace("rdb0.", "rdb4."),
                    "start_confl": options.start_conflicts}

        t = time.time()

        q = q_count + q_ok
        q = q.format(**myformat)
        if options.verbose:
            print("query:", q)
        cur = self.conn.execute(q.format(**myformat))
        num_lines_ok = int(cur.fetchone()[0])
        print("Num datapoints OK (K): %-3.5f" % (num_lines_ok/1000.0))

        q = q_count + q_bad
        q = q.format(**myformat)
        if options.verbose:
            print("query:", q)
        cur = self.conn.execute(q.format(**myformat))
        num_lines_bad = int(cur.fetchone()[0])
        print("Num datpoints BAD (K): %-3.5f" % (num_lines_bad/1000.0))

        total_lines = num_lines_ok + num_lines_bad
        print("Total number of datapoints (K): %-3.2f" % (total_lines/1000.0))
        if options.fixed_num_datapoints != -1:
            if options.fixed_num_datapoints > total_lines:
                print("WARNING -- Your fixed num datapoints is too high:", options.fixed_num_datapoints)
                print("WARNING -- We only have:", total_lines)
                print("WARNING --> Not returning data.")
                return False, None

        if total_lines == 0:
            print("WARNING: Total number of datapoints is 0. Potential issues:")
            print(" --> Minimum no. conflicts set too high")
            print(" --> Less than 1 restarts were made")
            print(" --> No conflicts in SQL")
            print(" --> Something went wrong")
            return False, None

        print("Percentage of OK: %-3.2f" % (num_lines_ok/float(total_lines)*100.0))
        q = q_ok_select + q_ok
        if options.fixed_num_datapoints != -1:
            myformat["limit"] = int(options.fixed_num_datapoints * num_lines_ok/float(total_lines))
            q += common_limits

        print("limit for OK:", myformat["limit"])
        q = q.format(**myformat)
        print("Running query for OK...")
        if options.verbose:
            print("query:", q)
        df = pd.read_sql_query(q, self.conn)

        q = q_bad_select + q_bad
        if options.fixed_num_datapoints != -1:
            myformat["limit"] = int(options.fixed_num_datapoints * num_lines_bad/float(total_lines))
            q += common_limits

        print("limit for bad:", myformat["limit"])
        q = q.format(**myformat)
        print("Running query for BAD...")
        if options.verbose:
            print("query:", q)
        df2 = pd.read_sql_query(q, self.conn)
        print("Queries finished. T: %-3.2f" % (time.time() - t))

        if options.dump_sql:
            print("-- query starts --")
            print(q)
            print("-- query ends --")

        return True, pd.concat([df, df2])


def get_one_file(dbfname):
    print("Using sqlite3db file %s" % dbfname)

    df = None
    with Query2(dbfname) as q:
        if not options.no_recreate_indexes:
            q.create_indexes()
        ok, df = q.get_clstats()
        if not ok:
            return False, None

        if options.verbose:
            print("Printing head:")
            print(df.head())
            print("Print head done.")

    return True, df


def transform(df):
    def check_clstat_row(self, row):
        if row[self.ntoc["cl.decision_level_hist"]] == 0 or \
                row[self.ntoc["cl.backtrack_level_hist"]] == 0 or \
                row[self.ntoc["cl.trail_depth_level_hist"]] == 0 or \
                row[self.ntoc["cl.vsids_vars_hist"]] == 0 or \
                row[self.ntoc["cl.size_hist"]] == 0 or \
                row[self.ntoc["cl.glue_hist"]] == 0 or \
                row[self.ntoc["cl.num_antecedents_hist"]] == 0:
            print("ERROR: Data is in error:", row)
            assert(False)
            exit(-1)

        return row

    # relative overlaps
    df["cl.overlap"] = df["cl.num_total_lits_antecedents"]-df["cl.size"]-2*df["cl.num_antecedents"]
    df["cl.overlap_rel"] = df["cl.overlap"]/df["cl.antec_overlap_hist"]
    df["cl.num_antecedents_rel"] = df["cl.num_antecedents"]/df["cl.num_antecedents_hist"]
    df["rst.varset_neg_polar_ratio"] = df["rst.varSetNeg"]/(df["rst.varSetPos"]+df["rst.varSetNeg"])

    # ************
    # TODO decision level and branch depth are the same, right???
    # ************
    df["cl.size_rel"] = df["cl.size"] / df["cl.size_hist"]
    df["cl.glue_rel_queue"] = df["cl.glue"] / df["cl.glue_hist_queue"]
    df["cl.glue_rel_long"] = df["cl.glue"] / df["cl.glue_hist_long"]
    df["cl.glue_rel"] = df["cl.glue"] / df["cl.glue_hist"]
    df["cl.trail_depth_level_rel"] = df["cl.trail_depth_level"]/df["cl.trail_depth_level_hist"]
    df["cl.branch_depth_rel_queue"] = df["cl.decision_level"]/df["cl.branch_depth_hist_queue"]

    # smaller-than larger-than for glue and size
    df["cl.size_smaller_than_hist"] = (df["cl.size"] < df["cl.size_hist"]).astype(int)
    df["cl.glue_smaller_than_hist"] = (df["cl.glue"] < df["cl.glue_hist"]).astype(int)
    df["cl.glue_smaller_than_hist_lt"] = (df["cl.glue"] < df["cl.glue_hist_long"]).astype(int)
    df["cl.glue_smaller_than_hist_queue"] = (df["cl.glue"] < df["cl.glue_hist_queue"]).astype(int)

    # relative decisions
    df["cl.decision_level_rel"] = df["cl.decision_level"]/df["cl.decision_level_hist"]
    df["cl.decision_level_pre1_rel"] = df["cl.decision_level_pre1"]/df["cl.decision_level_hist"]
    df["cl.decision_level_pre2_rel"] = df["cl.decision_level_pre2"]/df["cl.decision_level_hist"]
    df["cl.decision_level_pre2_rel"] = df["cl.decision_level_pre2"]/df["cl.decision_level_hist"]
    df["cl.decision_level_pre2_rel"] = df["cl.decision_level_pre2"]/df["cl.decision_level_hist"]
    df["cl.backtrack_level_rel"] = df["cl.backtrack_level"]/df["cl.decision_level_hist"]

    # relative props
    df["rst.all_props"] = df["rst.propBinRed"] + df["rst.propBinIrred"] + df["rst.propLongRed"] + df["rst.propLongIrred"]
    df["rst.propBinRed_ratio"] = df["rst.propBinRed"]/df["rst.all_props"]
    df["rst.propBinIrred_ratio"] = df["rst.propBinIrred"]/df["rst.all_props"]
    df["rst.propLongRed_ratio"] = df["rst.propLongRed"]/df["rst.all_props"]
    df["rst.propLongIrred_ratio"] = df["rst.propLongIrred"]/df["rst.all_props"]

    df["cl.trail_depth_level_rel"] = df["cl.trail_depth_level"]/df["rst.free"]

    # relative resolutions
    df["rst.resolBinIrred_ratio"] = df["rst.resolBinIrred"]/df["rst.resolutions"]
    df["rst.resolBinRed_ratio"] = df["rst.resolBinRed"]/df["rst.resolutions"]
    df["rst.resolLRed_ratio"] = df["rst.resolLRed"]/df["rst.resolutions"]
    df["rst.resolLIrred_ratio"] = df["rst.resolLIrred"]/df["rst.resolutions"]

    df["cl.num_antecedents_rel"] = df["cl.num_antecedents"] / df["cl.num_antecedents_hist"]
    df["cl.decision_level_rel"] = df["cl.decision_level"] / df["cl.decision_level_hist"]
    df["cl.trail_depth_level_rel"] = df["cl.trail_depth_level"] / df["cl.trail_depth_level_hist"]
    df["cl.backtrack_level_rel"] = df["cl.backtrack_level"] / df["cl.backtrack_level_hist"]

    # smaller-or-greater comparisons
    df["cl.decision_level_smaller_than_hist"] = (df["cl.decision_level"] < df["cl.decision_level_hist"]).astype(int)
    df["cl.backtrack_level_smaller_than_hist"] = (df["cl.backtrack_level"] < df["cl.backtrack_level_hist"]).astype(int)
    df["cl.trail_depth_level_smaller_than_hist"] = (df["cl.trail_depth_level"] < df["cl.trail_depth_level_hist"]).astype(int)
    df["cl.num_antecedents_smaller_than_hist"] = (df["cl.num_antecedents"] < df["cl.num_antecedents_hist"]).astype(int)
    df["cl.antec_sum_size_smaller_than_hist"] = (df["cl.antec_sum_size_hist"] < df["cl.num_total_lits_antecedents"]).astype(int)
    df["cl.antec_overlap_smaller_than_hist"] = (df["cl.antec_overlap_hist"] < df["cl.overlap"]).astype(int)
    df["cl.overlap_smaller_than_hist"] = (df["cl.overlap"]<df["cl.antec_overlap_hist"]).astype(int)
    df["cl.branch_smaller_than_hist_queue"] = (df["cl.decision_level"]<df["cl.branch_depth_hist_queue"]).astype(int)



    # df["cl.vsids_vars_rel"] = df["cl.vsids_vars_avg"] / df["cl.vsids_vars_hist"]

    old = set(df.columns.values.flatten().tolist())
    df = df.dropna(how="all")
    new = set(df.columns.values.flatten().tolist())
    if len(old - new) > 0:
        print("ERROR: a NaN number turned up")
        print("columns: ", (old - new))
        assert(False)
        exit(-1)

    # making sure "x.class" is the last one
    new_no_class = list(new)
    new_no_class.remove("x.class")
    df = df[new_no_class + ["x.class"]]

    return df


def dump_dataframe(df, name):
    if options.dump_csv:
        fname = "%s.csv" % name
        print("Dumping CSV data to:", fname)
        df.to_csv(fname, index=False, columns=sorted(list(df)))

    fname = "%s-pandasdata.dat" % name
    print("Dumping pandas data to:", fname)
    with open(fname, "wb") as f:
        pickle.dump(df, f)


def one_predictor(dbfname):
    ok, df = get_one_file(dbfname)
    if not ok:
        return False, None

    cleanname = re.sub('\.cnf.gz.sqlite$', '', dbfname)

    if options.verbose:
        print("Describing----")
        dat = df.describe()
        print(dat)
        print("Describe done.---")
        print("Features: ", df.columns.values.flatten().tolist())

    df = transform(df)

    if options.verbose:
        print("Describing post-transform ----")
        print(df.describe())
        print("Describe done.---")

    dump_dataframe(df, cleanname)

    return True, df


if __name__ == "__main__":
    usage = "usage: %prog [options] file1.sqlite [file2.sqlite ...]"
    parser = optparse.OptionParser(usage=usage)

    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")

    parser.add_option("--csv", action="store_true", default=False,
                      dest="dump_csv", help="Dump CSV (for weka)")

    parser.add_option("--sql", action="store_true", default=False,
                      dest="dump_sql", help="Dump SQL query")

    parser.add_option("--fixed", default=-1, type=int,
                      dest="fixed_num_datapoints", help="Exact number of examples to take. -1 is to take all. Default: %default")

    parser.add_option("--start", default=-1, type=int,
                      dest="start_conflicts", help="Only consider clauses from conflicts that are at least this high")

    parser.add_option("--noind", action="store_true", default=False,
                      dest="no_recreate_indexes", help="Don't recreate indexes")

    (options, args) = parser.parse_args()

    if len(args) < 1:
        print("ERROR: You must give at least one file")
        exit(-1)

    np.random.seed(2097483)
    dfs = []
    for dbfname in args:
        print("----- INTERMEDIATE predictor -------")
        ok, df = one_predictor(dbfname)
        if ok:
            dfs.append(df)

    if len(dfs) == 0:
        print("Error, nothing got ingested, something is off")
        exit(-1)

    # intermediate predictor is final
    if len(args) == 1:
        exit(0)

    print("----- FINAL predictor -------")
    if len(dfs) == 0:
        print("Ooops, final predictor is None, probably no meaningful data. Exiting.")
        exit(0)

    final_df = pd.concat(dfs)
    dump_dataframe(final_df, "final")
