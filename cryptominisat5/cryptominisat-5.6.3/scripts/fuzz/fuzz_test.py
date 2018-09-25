#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright (C) 2014  Mate Soos
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

from __future__ import with_statement  # Required in 2.5
from __future__ import print_function
import subprocess
import os
import sys
import time
import random
from random import choice
import optparse
import glob
import resource
from verifier import *
from functools import partial

print("our CWD is: %s files here: %s" % (os.getcwd(), glob.glob("*")))
sys.path.append(os.getcwd())
print("our sys.path is", sys.path)

from debuglib import *


class PlainHelpFormatter(optparse.IndentedHelpFormatter):

    def format_description(self, description):
        if description:
            return description + "\n"
        else:
            return ""


usage = "usage: %prog [options] --fuzz/--regtest/--checkdir/filetocheck"
desc = """Fuzz the solver with fuzz-generator: ./fuzz_test.py
"""


def set_up_parser():
    parser = optparse.OptionParser(usage=usage, description=desc,
                                   formatter=PlainHelpFormatter())
    parser.add_option("--exec", metavar="SOLVER", dest="solver",
                      default="../../build/cryptominisat5",
                      help="SAT solver executable. Default: %default")

    parser.add_option("--extraopts", "-e", metavar="OPTS",
                      dest="extra_options", default="",
                      help="Extra options to give to SAT solver")

    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")

    # for fuzz-testing
    parser.add_option("--seed", dest="fuzz_seed_start",
                      help="Fuzz test start seed. Otherwise, random seed is picked"
                      " (printed to console)", type=int)

    parser.add_option("--fuzzlim", dest="fuzz_test_lim", type=int,
                      help="Number of fuzz tests to run"
                      )
    parser.add_option("--novalgrind", dest="novalgrind", default=False,
                      action="store_true", help="No valgrind installed")
    parser.add_option("--valgrindfreq", dest="valgrind_freq", type=int,
                      default=10, help="1 out of X times valgrind will be used. Default: %default in 1")

    parser.add_option("--small", dest="small", default=False,
                      action="store_true",
                      help="Don't run 'large' fuzzer"
                      " (may mem-out on smaller systems)")
    parser.add_option("--gauss", dest="gauss", default=False,
                      action="store_true",
                      help="Concentrate fuzzing gauss")
    parser.add_option("--indep", dest="only_indep", default=False,
                      action="store_true",
                      help="Concentrate fuzzing independent variables")
    parser.add_option("--dump", dest="only_dump", default=False,
                      action="store_true",
                      help="Concentrate fuzzing dumped clauses")

    parser.add_option("--maxth", "-m", dest="max_threads", default=100,
                      type=int, help="Max number of threads")

    parser.add_option("--tout", "-t", dest="maxtime", type=int, default=35,
                      help="Max time to run. Default: %default")

    parser.add_option("--textra", dest="maxtimediff", type=int, default=10,
                      help="Extra time on top of timeout for processing."
                      " Default: %default")
    return parser


def fuzzer_call_failed(fname):
    print("OOps, fuzzer executable call failed!")
    print("Did you build with cmake -DENABLE_TESTING=ON? Did you do git submodules init & update?")
    print("Here is the output:")

    print("**** ----- ****")
    with open(fname, "r") as a:
        for x in a:
            print(x.strip())
    print("**** ----- ****")
    exit(-1)


class create_fuzz:

    def call_from_fuzzer(self, fuzzer, fname):
        seed = random.randint(0, 1000000)
        if len(fuzzer) == 1:
            call = "{0} {1} > {2}".format(fuzzer[0], seed, fname)
        elif len(fuzzer) == 2:
            call = "{0} {1} {2} > {3}".format(
                fuzzer[0], fuzzer[1], seed, fname)
        elif len(fuzzer) == 3:
            hashbits = (random.getrandbits(20) % 80) + 1
            call = "%s %s %d %s %d > %s" % (
                fuzzer[0], fuzzer[1], hashbits, fuzzer[2], seed, fname)
        else:
            assert False, "Fuzzer must have at most 2 arguments"

        return call

    def create_fuzz_file(self, fuzzer, fuzzers, fname):
        # handle special fuzzer
        fnames_multi = []
        if len(fuzzer) == 2 and fuzzer[1] == "special":

            # sometimes just fuzz with all SAT problems
            fixed = random.getrandbits(1) == 1

            for _ in range(random.randrange(2, 4)):
                fname2 = unique_file("fuzzTest")
                fnames_multi.append(fname2)

                # chose a ranom fuzzer, not multipart
                fuzzer2 = ["multipart.py", "special"]
                while os.path.basename(fuzzer2[0]) == "multipart.py":
                    fuzzer2 = choice(fuzzers)

                # sometimes fuzz with SAT problems only
                if (fixed):
                    fuzzer2 = fuzzers[0]

                print("fuzzer2 used: %s" % fuzzer2)
                call = self.call_from_fuzzer(fuzzer2, fname2)
                print("calling sub-fuzzer: %s" % call)
                status = subprocess.call(call, shell=True)
                if status != 0:
                    fuzzer_call_failed(fname2)

            # construct multi-fuzzer call
            call = ""
            call += fuzzer[0]
            call += " "
            for name in fnames_multi:
                call += " " + name
            call += " > " + fname

            return call, fnames_multi

        # handle normal fuzzer
        else:
            return self.call_from_fuzzer(fuzzer, fname), []


def file_exists(fname):
    try:
        with open(fname):
            return True
    except IOError:
        return False


def print_version():
    command = options.solver + " --version"
    if options.verbose:
        print("Executing: %s" % command)
    p = subprocess.Popen(command.rsplit(), stderr=subprocess.STDOUT,
            stdout=subprocess.PIPE, universal_newlines=True)

    consoleOutput, err = p.communicate()
    print("Version values: %s" % consoleOutput.strip())


class Tester:

    def __init__(self):
        self.ignoreNoSolution = False
        self.extra_opts_supported = self.list_options_if_supported(
            ["xor", "autodisablegauss", "sql", "clid"])
        self.sol_parser = solution_parser(options)
        self.sqlitedbfname = None
        self.clid_added = False
        self.only_indep = False
        self.indep_vars = []
        self.dump_red = None

    def list_options_if_supported(self, tocheck):
        ret = []
        for elem in tocheck:
            if self.option_supported(elem):
                ret.append(elem)

        return ret

    def option_supported(self, option_name):
        command = options.solver
        command += " --hhelp"
        p = subprocess.Popen(
            command.rsplit(), stderr=subprocess.STDOUT,
            stdout=subprocess.PIPE,
            universal_newlines=True)

        consoleOutput, err = p.communicate()

        for l in consoleOutput.split("\n"):
            tmp_option_name = "--" + option_name
            if tmp_option_name in l:
                return True

        return False

    def create_rnd_sched(self, string_list):
        opts = string_list.split(",")
        opts = [a.strip(" ") for a in opts]
        opts = sorted(list(set(opts)))
        if options.verbose:
            print("available schedule options: %s" % opts)

        sched = []
        for _ in range(int(random.gammavariate(12, 0.7))):
            sched.append(random.choice(opts))

        # just so that XOR is really found and used, so we can fuzz it
        if "autodisablegauss" in self.extra_opts_supported:
            if random.choice([False, True, True, True]) and self.this_gauss_on:
                sched.append("occ-xor")

        return sched

    def rnd_schedule_all(self, preproc):
        sched_opts = "handle-comps,"
        sched_opts += "scc-vrepl, cache-clean, cache-tryboth,"
        sched_opts += "sub-impl, intree-probe, probe,"
        sched_opts += "sub-str-cls-with-bin, distill-cls, scc-vrepl, sub-impl,"
        sched_opts += "sub-cls-with-bin,"
        sched_opts += "str-impl, cache-clean, sub-str-cls-with-bin, distill-cls, scc-vrepl,"
        sched_opts += "occ-backw-sub-str, occ-xor, occ-clean-implicit, occ-bve, occ-bva,"
        sched_opts += "check-cache-size, renumber"

        # type of schedule
        cmd = ""
        sched = ",".join(self.create_rnd_sched(sched_opts))
        if sched != "" and not preproc:
            cmd += "--schedule %s " % sched

        sched = ",".join(self.create_rnd_sched(sched_opts))
        if sched != "":
            cmd += "--preschedule %s " % sched

        return cmd

    def random_options(self, preproc=False):
        self.sqlitedbfname = None
        self.clid_added = False
        cmd = " --zero-exit-status "

        # disable gauss when gauss is compiled in but asked not to be used
        if not self.this_gauss_on and "autodisablegauss" in self.extra_opts_supported:
            cmd += "--maxgaussdepth 0 "

        # note, presimp=0 is braindead for preproc but it's mostly 1 so OK
        cmd += "--presimp %d " % random.choice([1, 1, 1, 1, 1, 1, 1, 0])
        cmd += "--confbtwsimp %d " % random.choice([100, 1000])

        if self.dump_red is not None:
            cmd += "--dumpred %s " % self.dump_red
            cmd += "--dumpredmaxlen %d " % random.choice([2, 10, 100, 100000])
            cmd += "--dumpredmaxglue %d " % random.choice([2, 10, 100, 100000])

        if self.only_indep:
            cmd += "--onlyindep "
            cmd += "--indep "
            cmd += ",".join(["%s" % x for x in self.indep_vars]) + " "

        if random.choice([True, False]) and "clid" in self.extra_opts_supported:
            cmd += "--varsperxorcut %d " % random.randint(4, 6)
            cmd += "--xorcache %d " % random.choice([0, 1])
            if random.choice([True, True, True, False]):
                self.clid_added = True
                cmd += "--clid "
            cmd += "--locgmult %.12f " % random.gammavariate(0.5, 0.7)
            cmd += "--varelimover %d " % random.gammavariate(1, 20)
            cmd += "--memoutmult %0.12f " % random.gammavariate(0.03, 50)
            cmd += "--verb %d " % random.choice([0, 0, 0, 0, 1, 2])
            cmd += "--maple %d " % random.choice([0, 1])
            if random.randint(0, 2) == 1:
                cmd += "--reconf %d " % random.choice([3, 4, 6, 7, 12, 13, 14, 15, 16])
            # cmd += "--undef %d " % random.choice([0, 1])
            cmd += " --reconfat %d " % random.randint(0, 2)
            cmd += "--ml  %s " % random.randint(0, 10)
            cmd += "--restart %s " % random.choice(
                ["geom", "glue", "luby"])
            cmd += "--adjustglue %f " % random.choice([0, 0.5, 0.7, 1.0])
            cmd += "--gluehist %s " % random.randint(1, 500)
            cmd += "--updateglueonanalysis %s " % random.randint(0, 1)
            cmd += "--otfhyper %s " % random.randint(0, 1)
            # cmd += "--clean %s " % random.choice(["size", "glue", "activity",
            # "prconf"])
            cmd += "--bothprop %s " % random.randint(0, 1)
            cmd += "--probemaxm %s " % random.choice([0, 10, 100, 1000])
            cmd += "--cachesize %s " % random.randint(10, 100)
            cmd += "--cachecutoff %s " % random.randint(0, 2000)
            cmd += "--occredmax %s " % random.randint(0, 100)
            cmd += "--extscc %s " % random.randint(0, 1)
            cmd += "--distill %s " % random.randint(0, 1)
            cmd += "--recur %s " % random.randint(0, 1)
            cmd += "--compsfrom %d " % random.randint(0, 2)
            cmd += "--compsvar %d " % random.randint(20000, 500000)
            cmd += "--compslimit %d " % random.randint(0, 3000)
            cmd += "--implicitmanip %s " % random.randint(0, 1)
            cmd += "--occsimp %s " % random.randint(0, 1)
            cmd += "--occirredmaxmb %s " % random.gammavariate(0.2, 5)
            cmd += "--occredmaxmb %s " % random.gammavariate(0.2, 5)
            cmd += "--skipresol %d " % random.choice([1, 1, 1, 0])
            cmd += "--implsubsto %s " % random.choice([0, 10, 1000])
            cmd += "--sync %d " % random.choice([100, 1000, 6000, 100000])
            cmd += "-m %0.12f " % random.gammavariate(0.1, 5.0)
            cmd += "--maxsccdepth %d " % random.choice([0, 1, 100, 100000])

            # more more minim
            cmd += "--moremoreminim %d " % random.choice([1, 1, 1, 0])
            cmd += "--moremorecachelimit %d " % int(random.gammavariate(1, 6))
            cmd += "--moremorestamp %d " % random.choice([1, 1, 1, 0])
            cmd += "--moremorealways %d " % random.choice([1, 1, 1, 0])

            if self.this_gauss_on:
                # Reduce iteratively the matrix that is updated
                cmd += "--iterreduce %s " % random.choice([0, 1])

                # Only run Gaussian Elimination until this depth
                cmd += "--maxgaussdepth %s " % int(random.gammavariate(1, 20.0))

                # Set maximum no. of rows for gaussian matrix."
                cmd += "--maxmatrixrows %s " % int(random.gammavariate(5, 15.0))

                # "Automatically disable gauss when performing badly")
                cmd += "--autodisablegauss %s " % random.choice([0, 1])

                # "Set minimum no. of rows for gaussian matrix.
                cmd += "--minmatrixrows %s " % int(random.gammavariate(3, 15.0))

                # Save matrix every Nth decision level."
                cmd += "--savematrix %s " % (int(random.gammavariate(1, 15.0))+1)

                # "Maximum number of matrixes to treat.")
                cmd += "--maxnummatrixes %s " % int(random.gammavariate(1, 10.0))

            if "sql" in self.extra_opts_supported and random.randint(0, 3) > 0 and self.num_threads == 1 and not self.preproc:
                cmd += "--sql 2 "
                self.sqlitedbfname = unique_file("fuzz", ".sqlitedb")
                cmd += "--sqlitedb %s " % self.sqlitedbfname
                cmd += "--sqlresttime %d " % random.randint(0, 1)
                cmd += "--cldatadumpratio %0.3f " % random.choice([0.9, 0.1, 0.7])

        # the most buggy ones, don't turn them off much, please
        if random.choice([True, False]):
            opts = ["scc", "varelim", "comps", "strengthen", "probe", "intree",
                    "stamp", "cache", "otfsubsume",
                    "renumber", "savemem", "moreminim", "gates", "bva",
                    "gorshort", "gandrem", "gateeqlit", "schedsimp"]

            if "xor" in self.extra_opts_supported:
                opts.append("xor")

            for opt in opts:
                cmd += "--%s %d " % (opt, random.randint(0, 1))

            cmd += self.rnd_schedule_all(preproc)

        return cmd

    def execute(self, fname, fname2=None, fixed_opts="", rnd_opts=None):
        if os.path.isfile(options.solver) is not True:
            print("Error: Cannot find CryptoMiniSat executable.Searched in: '%s'" %
                  options.solver)
            print("Error code 300")
            exit(300)

        for f in glob.glob("%s-debugLibPart*.output" % fname):
            os.unlink(f)

        # construct command
        command = ""
        if not options.novalgrind and random.randint(1, options.valgrind_freq) == 1:
            command += "valgrind -q --leak-check=full  --error-exitcode=9 "
        command += options.solver
        if rnd_opts is None:
            rnd_opts = self.random_options()
        command += rnd_opts
        if self.needDebugLib:
            command += "--debuglib %s " % fname
        command += "--threads %d " % self.num_threads
        command += options.extra_options + " "
        command += fixed_opts + " "
        if fname is not None:
            command += fname
        if fname2:
            if self.drat:
                command += " %s " % fname2
            else:
                command += " %s --savedstate %s-savedstate.dat " % (fname2, fname2)

        print("Executing: %s " % command)

        # print time limit
        if options.verbose:
            print("CPU limit of parent (pid %d)" % os.getpid(), resource.getrlimit(resource.RLIMIT_CPU))

        # if need time limit, then limit
        err_fname = unique_file("err", ".out")
        err_file = open(err_fname, "w")
        p = subprocess.Popen(
            command.rsplit(), stderr=err_file, stdout=subprocess.PIPE,
            preexec_fn=partial(setlimits, options.maxtime),
            universal_newlines=True)

        # print time limit after child startup
        if options.verbose:
            print("CPU limit of parent (pid %d) after startup of child: %s secs" %
                  (os.getpid(), resource.getrlimit(resource.RLIMIT_CPU)))

        # Get solver output
        consoleOutput, err = p.communicate()
        retcode = p.returncode
        err_file.close()
        with open(err_fname, "r") as err_file:
            found_something = False
            for line in err_file:
                print("Error line while executing: %s" % line.strip())
                # don't error out on issues related to UBSAN/ASAN
                # of clang of other projects
                if "std::_Ios_Fmtflags" in line or "mzd.h" in line or "lexical_cast.hpp" in line or "MersenneTwister.h" in line:
                    pass
                else:
                    found_something = True

            if found_something:
                exit(-1)

        os.unlink(err_fname)
        if self.sqlitedbfname is not None:
            os.unlink(self.sqlitedbfname)

        if options.verbose:
            print("CPU limit of parent (pid %d) after child finished executing: %s" %
                  (os.getpid(), resource.getrlimit(resource.RLIMIT_CPU)))

        return consoleOutput, retcode

    def check(self, fname, fname2=None,
              checkAgainst=None,
              fixed_opts="", dump_output_fname=None,
              rnd_opts=None):

        consoleOutput = ""
        if checkAgainst is None:
            checkAgainst = fname
        curr_time = time.time()

        # Do we need to solve the problem, or is it already solved?
        consoleOutput, retcode = self.execute(
            fname, fname2=fname2,
            fixed_opts=fixed_opts, rnd_opts=rnd_opts)

        # if time was limited, we need to know if we were over the time limit
        # and that is why there is no solution
        diff_time = time.time() - curr_time
        if diff_time > (options.maxtime - options.maxtimediff) / self.num_threads:
            print("Too much time to solve, aborted!")
            return None

        print("Within time limit: %.2f s" % diff_time)
        print("filename: %s" % fname)

        if options.verbose:
            print(consoleOutput)

        # if library debug is set, check it
        if (self.needDebugLib):
            self.sol_parser.check_debug_lib(checkAgainst)

        if retcode != 0:
            print("Return code is not 0, error!")
            exit(-1)

        print("Checking console output...")
        unsat, solution, _ = self.sol_parser.parse_solution_from_output(
            consoleOutput.split("\n"), self.ignoreNoSolution)

        # preprocessing
        if dump_output_fname is not None:
            f = open(dump_output_fname, "w")
            f.write(consoleOutput)
            f.close()
            return True

        if not unsat:
            if len(self.indep_vars) != 0:
                self.sol_parser.indep_vars_solution_check(fname, self.indep_vars, solution)
            else:
                self.sol_parser.test_found_solution(solution, checkAgainst)

            if self.dump_red:
                self.check_dumped_clauses(fname)

            return

        # it's UNSAT, let's check with DRAT
        if fname2:
            toexec = "../../build/tests/drat-trim/drat-trim {cnf} {dratf} {opt}"
            opt = ""
            if self.clid_added:
                opt = "-i "
            toexec = toexec.format(cnf=fname, dratf=fname2, opt=opt)
            print("Checking DRAT...: ", toexec)
            p = subprocess.Popen(toexec.rsplit(),
                    stdout=subprocess.PIPE,
                    universal_newlines=True)

            consoleOutput2 = p.communicate()[0]
            diff_time = time.time() - curr_time

            # find verification code
            foundVerif = False
            dratLine = ""
            for line in consoleOutput2.split('\n'):
                if len(line) > 1 and line[:2] == "s ":
                    # print("verif: " , line)
                    foundVerif = True
                    if line[2:10] != "VERIFIED" and line[2:] != "TRIVIAL UNSAT":
                        print("DRAT verification error, it says: %s" % consoleOutput2)
                    assert line[2:10] == "VERIFIED" or line[
                        2:] == "TRIVIAL UNSAT", "DRAT didn't verify problem!"
                    dratLine = line

            # Check whether we have found a verification code
            if foundVerif is False:
                print("verifier error! It says: %s" % consoleOutput2)
                assert foundVerif, "Cannot find DRAT verification code!"
            else:
                print("OK, DRAT says: %s" % dratLine)

        # check with other solver
        ret = self.sol_parser.check_unsat(checkAgainst)
        if ret is None:
            print("Other solver time-outed, cannot check")
        elif ret is True:
            print("UNSAT verified by other solver")
        else:
            print("Grave bug: SAT-> UNSAT : Other solver found solution!!")
            exit()

    def check_dumped_clauses(self, fname):
        assert self.dump_red is not None

        tmpfname = unique_file("fuzzTest-dump-test")
        with open(tmpfname, "w") as tmpf:
            with open(fname, "r") as x:
                for line in x:
                    line = line.strip()
                    if "c" in line or "p" in line:
                        continue
                    tmpf.write(line+"\n")

            with open(self.dump_red, "r") as x:
                for line in x:
                    line = line.strip()
                    tmpf.write(line+"\n")

        print("[dump-check] dump-combined file is: ", tmpfname)
        if options.verbose:
            print("dump file is:     ", self.dump_red)
            print("orig file is:     ",  fname)

        self.old_dump_red = str(self.dump_red)
        self.dump_red = None
        self.indep_vars = []
        self.only_indep = False
        self.check(tmpfname, checkAgainst=fname)

        os.unlink(tmpfname)
        os.unlink(self.old_dump_red)
        print("[dump-check] OK, solution after DUMP has been injected is still OK")

    def fuzz_test_one(self):
        print("--- NORMAL TESTING ---")
        self.num_threads = random.choice([1, 1, 1, 1, 1, 1, 4])
        self.num_threads = min(options.max_threads, self.num_threads)
        self.this_gauss_on = "autodisablegauss" in self.extra_opts_supported and random.choice([True, False, False])
        if options.gauss:
            self.this_gauss_on = True
            assert "autodisablegauss" in self.extra_opts_supported

        self.drat = self.num_threads == 1 and random.randint(0, 10) < 5 and (not self.this_gauss_on)
        self.sqlitedbfname = None
        self.preproc = False
        self.dump_red = random.choice([None, None, None, None, None, True])
        if self.dump_red is not None:
            self.dump_red = unique_file("fuzzTest-dump")
        self.only_indep = random.choice([True, False, False, False, False]) and not self.drat

        if options.only_indep:
            self.drat = False
            self.only_indep = True

        if options.only_dump:
            self.drat = False
            self.only_indep = False
            if self.dump_red is None:
                self.dump_red = unique_file("fuzzTest-dump")

        if self.drat:
            fuzzers = fuzzers_drat
        elif options.gauss:
            fuzzers = fuzzers_xor
        else:
            fuzzers = fuzzers_nodrat
        fuzzer = random.choice(fuzzers)

        fname = unique_file("fuzzTest")
        fname_drat = None
        if self.drat:
            fname_drat = unique_file("fuzzTest-drat")

        # create the fuzz file
        cf = create_fuzz()
        call, todel = cf.create_fuzz_file(fuzzer, fuzzers, fname)
        print("calling %s" % call)
        status = subprocess.call(call, shell=True)
        if status != 0:
            fuzzer_call_failed(fname)

        if not self.drat and not self.only_indep and not self.dump_red:
            self.needDebugLib = True
            interspersed_fname = unique_file("fuzzTest")
            seed_for_inters = random.randint(0, 1000000)
            intersperse(fname, interspersed_fname, seed_for_inters)
            print("Interspersed: ./intersperse.py %s %s %d" % (fname,
                                                               interspersed_fname,
                                                               seed_for_inters))
            os.unlink(fname)
        else:
            self.needDebugLib = False
            interspersed_fname = fname

        # calculate indep vars
        self.indep_vars = []
        if self.only_indep:
            max_vars = self.sol_parser.max_vars_in_file(fname)
            assert max_vars > 0

            self.indep_vars = []
            myset = {}
            for _ in range(random.randint(1, 50)):
                x = random.randint(1, max_vars)
                if x not in myset:
                    self.indep_vars.append(x)
                    myset[x] = 1

            # don't do it for 0-length indep vars
            if len(self.indep_vars) == 0:
                self.only_indep = False

        self.check(fname=interspersed_fname, fname2=fname_drat)

        # remove temporary filenames
        os.unlink(interspersed_fname)
        if fname_drat:
            os.unlink(fname_drat)
        for name in todel:
            os.unlink(name)

        if self.dump_red is not None:
            os.unlink(self.dump_red)
            self.dump_red = None

    def delete_file_no_matter_what(self, fname):
        try:
            os.unlink(fname)
        except:
            pass

    def fuzz_test_preproc(self):
        print("--- PREPROC TESTING ---")
        self.this_gauss_on = False  # don't do gauss on preproc
        tester.needDebugLib = False
        fuzzer = random.choice(fuzzers_drat)
        self.num_threads = 1
        fname = unique_file("fuzzTest")
        self.drat = False
        self.preproc = True
        self.only_indep = False
        self.indep_vars = []
        assert self.dump_red is None
        self.dump_red = None

        # create the fuzz file
        cf = create_fuzz()
        call, todel = cf.create_fuzz_file(fuzzer, fuzzers_nodrat, fname)
        print("calling %s : %s" % (fuzzer, call))
        status = subprocess.call(call, shell=True)
        if status != 0:
            fuzzer_call_failed(fname)

        rnd_opts = self.random_options(preproc=True)

        # preprocess
        simp = "%s-simplified.cnf" % fname
        self.delete_file_no_matter_what(simp)
        curr_time = time.time()
        console, retcode = self.execute(fname, fname2=simp,
                                        rnd_opts=rnd_opts,
                                        fixed_opts="--preproc 1")

        diff_time = time.time() - curr_time
        if diff_time > (options.maxtime - options.maxtimediff) / self.num_threads:
            print("Too much time to solve, aborted!")
        else:
            print("Within time limit: %.2f s" % diff_time)
            if retcode != 0:
                print("Return code is not 0, error!")
                exit(-1)

            solution = "%s-solution.sol" % fname
            ret = self.check(fname=simp, dump_output_fname=solution)
            if ret is not None:
                # didn't time out, so let's reconstruct the solution
                savedstate = "%s-savedstate.dat" % simp
                self.check(fname=solution, checkAgainst=fname,
                           fixed_opts="--preproc 2 --savedstate %s" % savedstate,
                           rnd_opts=rnd_opts)
                os.unlink(savedstate)
                os.unlink(solution)

        # remove temporary filenames
        os.unlink(fname)
        for name in todel:
            os.unlink(name)
        assert self.dump_red is None


def filter_large_fuzzer(dat):
    f = []
    for x in dat:
        okay = True
        for y in x:
            if "large" in y:
                okay = False

        if okay:
            f.append(x)

    return f


fuzzers_noxor = [
    ["../../build/tests/sha1-sat/sha1-gen --nocomment --attack preimage --rounds 20",
     "--hash-bits", "--seed"],
    ["../../build/tests/sha1-sat/sha1-gen --nocomment --attack preimage --zero "
        "--message-bits 400 --rounds 8 --hash-bits 60",
     "--seed"],
    # ["build/cnf-fuzz-nossum"],
    ["../../build/tests/cnf-utils/largefuzzer"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/cnf-fuzz-biere"],
    ["../../build/tests/cnf-utils/sgen4 -unsat -n 50", "-s"],
    ["../../build/tests/cnf-utils//sgen4 -sat -n 50", "-s"],
    ["../../utils/cnf-utils/cnf-fuzz-brummayer.py", "-s"],
    ["../../utils/cnf-utils/cnf-fuzz-xor.py", "--seed"],
    ["../../utils/cnf-utils/multipart.py", "special"]
]
fuzzers_xor = [
    ["../../utils/cnf-utils/xortester.py", "--seed"],
    ["../../build/tests/sha1-sat/sha1-gen --xor --attack preimage --rounds 21",
     "--hash-bits", "--seed"],
]


if __name__ == "__main__":
    global options
    global fuzzers_drat
    global fuzzers_nodrat
    if not os.path.isdir("out"):
        print("Directory for outputs, 'out' not present, creating it.")
        os.mkdir("out")

    # parse options
    parser = set_up_parser()
    (options, args) = parser.parse_args()
    if options.valgrind_freq <= 0:
        print("Valgrind Frequency must be at least 1")
        exit(-1)

    fuzzers_drat = fuzzers_noxor
    fuzzers_nodrat = fuzzers_noxor + fuzzers_xor
    if options.small:
        fuzzers_drat = filter_large_fuzzer(fuzzers_drat)
        fuzzers_nodrat = filter_large_fuzzer(fuzzers_nodrat)

    print_version()
    tester = Tester()
    tester.needDebugLib = False
    num = 0
    rnd_seed = options.fuzz_seed_start
    if rnd_seed is None:
        rnd_seed = random.randint(0, 1000*1000*100)

    while True:
        toexec = "./fuzz_test.py --fuzzlim 1 --seed %d " % rnd_seed
        if options.novalgrind:
            toexec += "--novalgrind "
        if options.valgrind_freq:
            toexec += "--valgrindfreq %d " % options.valgrind_freq
        if options.small:
            toexec += "--small "
        if options.gauss:
            toexec += "--gauss "
        if options.only_indep:
            toexec += "--indep "
        if options.only_dump:
            toexec += "--dump "
        toexec += "-m %d " % options.max_threads

        print("")
        print("")
        print("--> To re-create fuzz-test below: %s" % toexec)

        random.seed(rnd_seed)
        if random.randint(0, 10) == 0:
            tester.fuzz_test_preproc()
        else:
            tester.fuzz_test_one()
        rnd_seed += 1
        num += 1
        if options.fuzz_test_lim is not None and num >= options.fuzz_test_lim:
            exit(0)
