#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright (C) 2018  Mate Soos
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

import optparse
import random
import time
import string
import configparser


def parse_arguments():
    class PlainHelpFormatter(optparse.IndentedHelpFormatter):

        def format_description(self, description):
            if description:
                return description + "\n"
            else:
                return ""

    usage = """usage: %prog

To use other solvers, give:
--solver SWDiA5BY.alt.vd.res.va2.15000.looseres.3tierC5/binary/SWDiA5BY_static.alt.vd
--solver SWDiA5BY_A26/binary/SWDiA5BY_static_A26
--solver lingeling_ayv/binary/lingeling_ayv
--solver glucose2016/simp/glucose_static_2016
--solver MapleCOMSPS/simp/maplecomsps_static
--solver cmsat-satcomp16/bin/cryptominisat4_simple
--solver lingeling-bbc/build/lingeling/lingeling_bbc
--solver Maple_LCM_Dist/Maple_LCM_Dist # may work with --drat, but needs updated DRAT checker


Use-cases:
# normal run
./launch_server.py --cnflist satcomp17_updated

# stats run
./launch_server.py --cnf test_updated --stats --drat --tout 600 --memlimit 10000
./launch_server.py --cnf unsat_small_candidates_fullpath --stats --drat --tout 600 --memlimit 10000


# testing, using small instance to check (cheaper & faster)
./launch_server.py --cnflist test_updated

# 2 clients, no preprocessing
./launch_server.py --cnflist satcomp14 -c 2 --opt "--preproc 0" --folder no_preproc

# gaussian elimination -- automatic detection, built with GAUSS
./launch_server.py --cnflist satcomp14 --folder gauss

# clause IDs so learning can be performed -- gzipped SQL output with clause IDs will be produced
./launch_server.py --stats --drat --folder learning

# to give options to the solver
./launch_server.py --folder with_opts --opt \"--ml=1,--keepglue=4\""

 # to upload features_to_reconf.cpp
aws s3 cp ../../src/features_to_reconf.cpp s3://msoos-solve-data/solvers/

"""
    parser = optparse.OptionParser(usage=usage, formatter=PlainHelpFormatter())
    parser.add_option("--verbose", "-v", action="store_true",
                      default=False, dest="verbose", help="Be more verbose"
                      )

    parser.add_option("--numclients", "-c", default=None, type=int,
                      dest="client_count", help="Number of clients to launch"
                      )

    parser.add_option("--port", "-p", default=10000, dest="port",
                      help="Port to listen on. [default: %default]", type="int"
                      )

    parser.add_option("--tout", "-t", default=3000, dest="timeout_in_secs",
                      help="Timeout for the file in seconds"
                      "[default: %default]",
                      type=int
                      )

    parser.add_option("--toutmult", default=12.1, dest="tout_mult",
                      help="Approx: 1x is solving, 10x time is DRAT time wait, 1x is parsing, 0.1x that is sending us the result."
                      "[default: %default]",
                      type=float
                      )

    parser.add_option("--memlimit", "-m", default=1600, dest="mem_limit_in_mb",
                      help="Memory limit in MB"
                      "[default: %default]",
                      type=int
                      )

    parser.add_option("--cnflist", default="satcomp14_updated", dest="cnf_list",
                      type=str,
                      help="The list of CNF files to solve, first line the dir"
                      "[default: %default]",
                      )

    parser.add_option("--dir", default="/home/ubuntu/", dest="base_dir", type=str,
                      help="The home dir of cryptominisat [default: %default]"
                      )

    parser.add_option("--solver",
                      default="cryptominisat/build/cryptominisat5",
                      dest="solver",
                      help="Solver executable"
                      "[default: %default]",
                      type=str
                      )

    parser.add_option("--folder", default="results", dest="given_folder",
                      help="S3 folder name to upload data"
                      "[default: %default]",
                      type=str
                      )

    parser.add_option("--git", dest="git_rev", type=str,
                      help="The GIT revision to use. Default: HEAD"
                      )

    parser.add_option("--opt", dest="extra_opts", type=str, default="",
                      help="Extra options to give to solver"
                      "[default: %default]",
                      )

    parser.add_option("--noshutdown", "-n", default=False, dest="noshutdown",
                      action="store_true", help="Do not shut down clients"
                      )

    parser.add_option("--drat", default=False, dest="drat",
                      action="store_true", help="Use DRAT"
                      )

    parser.add_option("--stats", default=False, dest="stats",
                      action="store_true", help="Use STATS and get SQLITE data"
                      )

    parser.add_option("--gauss", default=False, dest="gauss",
                      action="store_true", help="Use GAUSS"
                      )

    parser.add_option("--logfile", dest="logfile_name", type=str,
                      default="python_server_log.log", help="Name of LOG file")

    # parse options
    options, args = parser.parse_args()
    conf = configparser.ConfigParser()
    if options.cnf_list == "test":
        conf.read('ec2-spot-instance-test.cfg')
    else:
        conf.read('ec2-spot-instance.cfg')

    options.s3_bucket = conf.get("ec2", "result_bucket")
    options.key_name = conf.get("ec2", "key_name")
    options.security_group_server = conf.get("ec2", "security_group_server")
    options.subnet_id = conf.get("ec2", "subnet_id")
    options.ami_id = conf.get("ec2", "ami_id")
    options.region = conf.get("ec2", "region")

    def rnd_id():
        return ''.join(random.choice(string.ascii_uppercase + string.digits) for _ in range(5))

    options.logfile_name = options.base_dir + options.logfile_name
    options.given_folder += "-" + time.strftime("%d-%B-%Y")
    options.given_folder += "-%s" % rnd_id()
    options.given_folder += "-%s" % options.cnf_list

    if options.drat and not options.stats:
        print("ERROR: You must have --stats when you use --drat")
        exit(-1)

    return options, args


if __name__ == "__main__":
    options, args = parse_arguments()
    print("Options are:", options)
    print("args are:", args)
