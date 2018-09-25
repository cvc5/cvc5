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

from __future__ import print_function
import os
import socket
import sys
import optparse
import struct
import pickle
import threading
import random
import time
import subprocess
import resource
import pprint
import traceback
import boto
import boto.utils
import boto.ec2
import logging
import functools
import string

# for importing in systems where "." is not in the PATH
sys.path.append(os.getcwd()+"/scripts/learn/")
from common_aws import *
import add_lemma_ind as addlemm

pp = pprint.PrettyPrinter(depth=6)


class PlainHelpFormatter(optparse.IndentedHelpFormatter):

    def format_description(self, description):
        if description:
            return description + "\n"
        else:
            return ""


def uptime():
    with open('/proc/uptime', 'r') as f:
        return float(f.readline().split()[0])

    return None


def get_n_bytes_from_connection(sock, MSGLEN):
    chunks = []
    bytes_recd = 0
    while bytes_recd < MSGLEN:
        chunk = sock.recv(min(MSGLEN - bytes_recd, 2048))
        if chunk == '':
            raise RuntimeError("socket connection broken")
        chunks.append(chunk)
        bytes_recd = bytes_recd + len(chunk)

    return ''.join(chunks)


def connect_client(threadID):
    # Create a socket object
    sock = socket.socket()

    # Get local machine name
    if options.host is None:
        print("You must supply the host to connect to as a client")
        exit(-1)

    logging.info("Getting host by name %s", options.host,
                 extra={"threadid": threadID})
    host = socket.gethostbyname_ex(options.host)
    logging.info("Connecting to host %s", host,
                 extra={"threadid": threadID})
    sock.connect((host[2][0], options.port))

    return sock


def send_command(sock, command, tosend=None):
    # can't set tosend={} because of Python weirdness
    tosend = tosend or {}

    tosend["command"] = command
    tosend = pickle.dumps(tosend)
    tosend = struct.pack('!q', len(tosend)) + tosend
    sock.sendall(tosend)


def ask_for_data(sock, command, threadID):
    logging.info("Asking for %s", command, extra={"threadid": threadID})
    tosend = {}
    tosend["uptime"] = uptime()
    send_command(sock, command, tosend)

    # get stuff to solve
    data = get_n_bytes_from_connection(sock, 8)
    length = struct.unpack('!q', data)[0]
    data = get_n_bytes_from_connection(sock, length)
    indata = pickle.loads(data)
    return indata


def signal_error_to_master():
    sock = connect_client(100)
    send_command(sock, "error")
    sock.close()


def setlimits(time_limit, mem_limit):
        #logging.info(
            #"Setting resource limit in child (pid %d). Time %d s"
            #"Mem %d MB\n", os.getpid(), time_limit,
            #mem_limit,
            #extra=self.logextra)

        resource.setrlimit(resource.RLIMIT_CPU, (
            time_limit,
            time_limit))

        resource.setrlimit(resource.RLIMIT_DATA, (
            mem_limit * 1024 * 1024,
            mem_limit * 1024 * 1024))


class solverThread (threading.Thread):

    def __init__(self, threadID):
        threading.Thread.__init__(self)
        self.threadID = threadID
        self.logextra = {'threadid': self.threadID}
        self.temp_space = self.create_temp_space()
        logging.info("Initializing thread", extra=self.logextra)

    def create_temp_space(self):
        newdir = options.temp_space + "/thread-%s" % self.threadID
        try:
            os.system("sudo mkdir %s" % newdir)
            os.system("sudo chown ubuntu:ubuntu %s" % newdir)
        except:
            exc_type, exc_value, exc_traceback = sys.exc_info()
            the_trace = traceback.format_exc().rstrip().replace("\n", " || ")
            logging.warning("Error creating directory: %s",
                            the_trace, extra={"threadid": -1})

        return newdir

    def get_fname_no_dir(self):
        fname = self.indata["cnf_filename"]
        slash_at = fname.find("/")
        return fname[slash_at+1:]

    def get_tmp_cnf_fname(self):
        return "%s/%s" % (
            self.temp_space,
            self.get_fname_no_dir()
        )

    def get_stdout_fname(self):
        return self.get_tmp_cnf_fname() + "-" + self.indata["uniq_cnt"] + ".stdout"

    def get_stderr_fname(self):
        return self.get_tmp_cnf_fname() + "-" + self.indata["uniq_cnt"] + ".stderr"

    def get_sqlite_fname(self):
        return self.get_tmp_cnf_fname() + "-" + self.indata["uniq_cnt"] + ".sqlite"

    def get_lemmas_fname(self):
        return "%s/lemmas" % self.temp_space

    def get_drat_fname(self):
        return "%s/drat" % self.temp_space

    def get_toexec(self):
        logging.info("Getting file to solve {cnf}".format(cnf=self.indata["cnf_filename"]),
                extra=self.logextra)

        key = boto.connect_s3().get_bucket("msoos-solve-data").get_key(self.indata["cnf_filename"])
        key.get_contents_to_filename(self.get_tmp_cnf_fname())

        toexec = []
        toexec.append("%s/%s" % (options.base_dir, self.indata["solver"]))
        toexec.append(self.indata["extra_opts"].replace(",", " "))
        if "cryptominisat5" in self.indata["solver"]:
            toexec.append("--printsol 0")
            if self.indata["stats"]:
                toexec.append("--sql 2")
                toexec.append("--sqlitedb %s" % self.get_sqlite_fname())

        toexec.append(self.get_tmp_cnf_fname())
        if self.indata["drat"]:
            if "Maple" in self.indata["solver"]:
                toexec.extend(["-drup-file=%s" % self.get_drat_fname()])
            if "cryptominisat5" in self.indata["solver"]:
                toexec.extend(["--drat", self.get_drat_fname()])
                # never stop search() to simplify anything
                # toexec.append("-n 1")
                # toexec.append("--ml 0")
                # toexec.append("--gluecut0 100")
                # toexec.append("--otfsubsume 0")
                if self.indata["stats"]:
                    toexec.append("--clid")
        else:
            if "cryptominisat5" in self.indata["solver"] and self.indata["stats"]:
                toexec.append("--sqlfull 0")

        return " ".join(toexec)

    def execute_solver(self):
        toexec = self.get_toexec()
        stdout_file = open(self.get_stdout_fname(), "w")
        stderr_file = open(self.get_stderr_fname(), "w")

        # limit time
        limits_printed = "Thread %d executing '%s' with timeout %d s  and memout %d MB" % (
            self.threadID,
            toexec,
            self.indata["timeout_in_secs"],
            self.indata["mem_limit_in_mb"]
        )
        logging.info(limits_printed, extra=self.logextra)
        stderr_file.write(limits_printed + "\n")
        stderr_file.flush()
        stdout_file.write(limits_printed + "\n")
        stdout_file.flush()

        tstart = time.time()
        p = subprocess.Popen(
            toexec.rsplit(), stderr=stderr_file, stdout=stdout_file,
            preexec_fn=functools.partial(
                setlimits,
                self.indata["timeout_in_secs"],
                self.indata["mem_limit_in_mb"]))
        p.wait()
        tend = time.time()

        towrite = "Finished in %f seconds by thread %s return code: %d\n" % (
            tend - tstart, self.threadID, p.returncode)
        stderr_file.write(towrite)
        stdout_file.write(towrite)
        stderr_file.close()
        stdout_file.close()
        logging.info(towrite.strip(), extra=self.logextra)

        return p.returncode, toexec

    def run_drat_trim(self):
        toexec = "%s/drat-trim/drat-trim %s %s -x %s" % (
            options.base_dir,
            self.get_tmp_cnf_fname(),
            self.get_drat_fname(),
            self.get_lemmas_fname())
        logging.info("Current working dir: %s", os.getcwd(), extra=self.logextra)
        logging.info("Executing %s", toexec, extra=self.logextra)

        stdout_file = open(self.get_stdout_fname(), "a")
        stderr_file = open(self.get_stderr_fname(), "a")
        tstart = time.time()
        p = subprocess.Popen(
            toexec.rsplit(), stderr=stderr_file, stdout=stdout_file,
            preexec_fn=functools.partial(
                setlimits,
                10*self.indata["timeout_in_secs"],
                2*self.indata["mem_limit_in_mb"]))
        p.wait()
        tend = time.time()

        towrite = "Finished DRAT-TRIM2 in %f seconds by thread %s return code: %d\n" % (
            tend - tstart, self.threadID, p.returncode)
        stderr_file.write(towrite)
        stdout_file.write(towrite)
        stderr_file.close()
        stdout_file.close()

        return p.returncode

    def add_lemma_idx_to_sqlite(self, lemmafname, dbfname):
        logging.info("Updating sqlite with DRAT info."
                     "Using sqlite3db file %s. Using lemma file %s",
                     dbfname, lemmafname, extra=self.logextra)

        useful_lemma_ids = []
        with addlemm.Query(dbfname) as q:
            useful_lemma_ids = addlemm.parse_lemmas(lemmafname, q.runID)
            q.add_goods(useful_lemma_ids)

        logging.info("Num good IDs: %d",
                     len(useful_lemma_ids), extra=self.logextra)

        os.unlink(self.get_lemmas_fname())

    def create_url(self, bucket, folder, key):
        return 'https://%s.s3.amazonaws.com/%s/%s' % (bucket, folder, key)

    def rnd_id(self):
        return ''.join(random.choice(string.ascii_uppercase + string.digits) for _ in range(5))

    def copy_solution_to_s3(self):
        exists = boto_conn.lookup(self.indata["s3_bucket"])
        if not exists:
            boto_conn.create_bucket(self.indata["s3_bucket"])
        boto_bucket = boto_conn.get_bucket(self.indata["s3_bucket"])
        k = boto.s3.key.Key(boto_bucket)

        s3_folder = get_s3_folder(self.indata["given_folder"],
                                  self.indata["git_rev"],
                                  self.indata["solver"],
                                  self.indata["timeout_in_secs"],
                                  self.indata["mem_limit_in_mb"])

        s3_folder_and_fname = s3_folder + "/" + self.get_fname_no_dir() + "-" + self.indata["uniq_cnt"]
        s3_folder_and_fname_clean = s3_folder + "/" + self.get_fname_no_dir()

        toreturn = []

        # stdout
        ret = os.system("gzip -f %s" % self.get_stdout_fname())
        logging.info("Return from gzip '%s': %s", self.get_stdout_fname(),
                     ret, extra=self.logextra)
        fname = s3_folder_and_fname + ".stdout.gz-tmp" + self.rnd_id()
        fname_clean = s3_folder_and_fname_clean + ".stdout.gz"
        k.key = fname
        boto_bucket.delete_key(k)
        ret = k.set_contents_from_filename(self.get_stdout_fname() + ".gz")
        logging.info("Return from S3 writing file '%s': %s",
                     fname, ret, extra=self.logextra)
        toreturn.append([fname, fname_clean])

        # stderr
        ret = os.system("gzip -f %s" % self.get_stderr_fname())
        logging.info("Return from gzip '%s': %s", self.get_stderr_fname(),
                     ret, extra=self.logextra)
        fname = s3_folder_and_fname + ".stderr.gz-tmp" + self.rnd_id()
        fname_clean = s3_folder_and_fname_clean + ".stderr.gz"
        k.key = fname
        boto_bucket.delete_key(k)
        ret = k.set_contents_from_filename(self.get_stderr_fname() + ".gz")
        logging.info("Return from S3 writing file '%s': %s",
                     fname, ret, extra=self.logextra)
        toreturn.append([fname, fname_clean])

        # sqlite
        if "cryptominisat5" in self.indata["solver"] and self.indata["stats"]:
            ret = os.system("gzip -f %s" % self.get_sqlite_fname())
            logging.info("Return from gzip '%s': %s", self.get_sqlite_fname(),
                         ret, extra=self.logextra)
            fname = s3_folder_and_fname + ".sqlite.gz-tmp" + self.rnd_id()
            fname_clean = s3_folder_and_fname_clean + ".sqlite.gz"
            k.key = fname
            boto_bucket.delete_key(k)
            ret = k.set_contents_from_filename(self.get_sqlite_fname() + ".gz")
            logging.info("Return from S3 writing file '%s': %s",
                         fname, ret, extra=self.logextra)
            toreturn.append([fname, fname_clean])

        logging.info("Uploaded stdout+stderr+sqlite files: %s",
                     toreturn, extra=self.logextra)

        os.unlink(self.get_stdout_fname() + ".gz")
        os.unlink(self.get_stderr_fname() + ".gz")
        if "cryptominisat5" in self.indata["solver"] and self.indata["stats"]:
            os.unlink(self.get_sqlite_fname() + ".gz")

        return toreturn

    def run_loop(self):
        global exitapp
        num_connect_problems = 0
        while not exitapp:
            if (num_connect_problems >= 20):
                logging.error("Too many connection problems, exiting.",
                              extra=self.logextra)
                exitapp = True
                return

            time.sleep(random.randint(0, 100) / 20.0)
            try:
                sock = connect_client(self.threadID)
            except:
                exc_type, exc_value, exc_traceback = sys.exc_info()
                the_trace = traceback.format_exc().rstrip().replace("\n", " || ")
                logging.warn("Problem trying to connect"
                             "waiting and re-connecting."
                             " Trace: %s", the_trace,
                             extra=self.logextra)
                time.sleep(3)
                num_connect_problems += 1
                continue

            self.indata = ask_for_data(sock, "need", self.threadID)
            sock.close()

            logging.info("Got data from server %s",
                         pprint.pformat(self.indata, indent=4).replace("\n", " || "),
                         extra=self.logextra)
            options.noshutdown |= self.indata["noshutdown"]

            # handle 'finish'
            if self.indata["command"] == "finish":
                logging.warn("Client received that there is nothing more"
                             " to solve, exiting this thread",
                             extra=self.logextra)
                return

            # handle 'wait'
            if self.indata["command"] == "wait":
                time.sleep(20)
                continue

            # handle 'solve'
            if self.indata["command"] == "solve":
                returncode, executed = self.execute_solver()
                if returncode == 20 and self.indata["drat"] and self.indata["stats"]:
                    if self.run_drat_trim() == 0:
                        self.add_lemma_idx_to_sqlite(
                            self.get_lemmas_fname(),
                            self.get_sqlite_fname())
                os.unlink(self.get_tmp_cnf_fname())
                if self.indata["drat"]:
                    os.unlink(self.get_drat_fname())
                files = self.copy_solution_to_s3()
                self.send_back_that_we_solved(returncode, files)
                continue

            logging.error("Data unrecognised by client: %s, exiting",
                          self.logextra)
            return

        logging.info("Exit asked for by another thread. Exiting",
                     extra=self.logextra)

    def send_back_that_we_solved(self, returncode, files):
        logging.info("Trying to send to server that we are done",
                     extra=self.logextra)
        fail_connect = 0
        while True:
            if fail_connect > 5:
                logging.error("Too many errors connecting to server to"
                              " send results. Shutting down",
                              extra=self.logextra)
                shutdown(-1)
            try:
                sock = connect_client(self.threadID)
                break
            except:
                exc_type, exc_value, exc_traceback = sys.exc_info()
                the_trace = traceback.format_exc().rstrip().replace("\n", " || ")

                logging.warn("Problem, waiting and re-connecting."
                             " Trace: %s", the_trace,
                             extra=self.logextra)
                time.sleep(random.randint(0, 5) / 10.0)
                fail_connect += 1

        tosend = {}
        tosend["file_num"] = self.indata["file_num"]
        tosend["returncode"] = returncode
        tosend["files"] = files
        send_command(sock, "done", tosend)
        logging.info("Sent that we finished %s with retcode %d",
                     self.indata["file_num"], returncode, extra=self.logextra)

        sock.close()

    def run(self):
        logging.info("Starting thread", extra=self.logextra)
        global exitapp

        try:
            self.run_loop()
        except KeyboardInterrupt:
            exitapp = True
            raise
        except:
            exc_type, exc_value, exc_traceback = sys.exc_info()
            the_trace = traceback.format_exc().rstrip().replace("\n", " || ")

            exitapp = True
            logging.error("Unexpected error in thread: %s", the_trace,
                          extra=self.logextra)
            shutdown(-1)
            raise


def build_cryptominisat(indata):
    opts = []
    opts.append(indata["git_rev"])
    opts.append(str(options.num_threads))
    if indata["stats"]:
        opts.append("-DSTATS=ON")

    if indata["gauss"]:
        opts.append("-DUSE_GAUSS=ON")

    ret = os.system('%s/cryptominisat/scripts/aws/build_cryptominisat.sh %s >> %s/build.log 2>&1' %
                    (options.base_dir,
                     " ".join(opts),
                     options.base_dir))
    global s3_folder
    s3_folder = get_s3_folder(indata["given_folder"],
                              indata["git_rev"],
                              indata["solver"],
                              indata["timeout_in_secs"],
                              indata["mem_limit_in_mb"]
                              )
    global s3_bucket
    s3_bucket = indata["s3_bucket"]
    logging.info("s3 bucket: %, s3 folder: %", s3_bucket, s3_folder, extra={"threadid": "-1"})
    if ret != 0:
        logging.error("Error building cryptominisat, shutting down!",
                      extra={"threadid": -1}
                      )
        shutdown(-1)


def build_system():
    built_system = False
    logging.info("Building system", extra={"threadid": -1})
    tries = 0
    while not built_system and tries < 10:
        try:
            tries += 1
            sock = connect_client(-1)
        except Exception:
            exc_type, exc_value, exc_traceback = sys.exc_info()
            the_trace = traceback.format_exc().rstrip().replace("\n", " || ")
            logging.warning("Problem, waiting and re-connecting. Error: %s",
                            the_trace,
                            extra={"threadid": -1})
            time.sleep(3)
            continue

        indata = ask_for_data(sock, "build", -1)
        options.noshutdown |= indata["noshutdown"]
        sock.close()

        if "cryptominisat5" in indata["solver"]:
            build_cryptominisat(indata)

        built_system = True

    if not built_system:
        shutdown(-1)


def num_cpus():
    num_cpu = 0
    cpuinfo = open("/proc/cpuinfo", "r")
    for line in cpuinfo:
        if "processor" in line:
            num_cpu += 1

    cpuinfo.close()
    return num_cpu


def shutdown(exitval=0):
    toexec = "sudo shutdown -h now"
    logging.info("SHUTTING DOWN", extra={"threadid": -1})

    # signal error to master
    if exitval != 0:
        try:
            signal_error_to_master()
        except:
            pass

    # send email
    if exitval == 0:
        reason = "OK"
    else:
        reason = "FAIL"

    try:
        send_email("Client shutting down %s" % reason,
                   "Client finished.", options.logfile_name)
    except:
        exc_type, exc_value, exc_traceback = sys.exc_info()
        the_trace = traceback.format_exc().rstrip().replace("\n", " || ")
        logging.error("Cannot send email! Traceback: %s", the_trace,
                      extra={"threadid": -1})

    if not options.noshutdown:
        os.system(toexec)

    exit(exitval)


def set_up_logging():
    form = '[ %(asctime)-15s thread %(threadid)s '
    form += get_ip_address(options.network_device)
    form += " %(levelname)s  %(message)s ]"

    logformatter = logging.Formatter(form)

    consoleHandler = logging.StreamHandler()
    consoleHandler.setFormatter(logformatter)
    logging.getLogger().addHandler(consoleHandler)

    try:
        os.unlink(options.logfile_name)
    except:
        pass
    fileHandler = logging.FileHandler(options.logfile_name)
    fileHandler.setFormatter(logformatter)
    logging.getLogger().addHandler(fileHandler)

    logging.getLogger().setLevel(logging.INFO)


def update_num_threads():
    if options.num_threads is None:
        options.num_threads = num_cpus()/2
        options.num_threads = max(options.num_threads, 1)

    logging.info("Running with %d threads", options.num_threads,
                 extra={"threadid": -1})


def build_system_full():
    try:
        build_system()
    except:
        exc_type, exc_value, exc_traceback = sys.exc_info()
        the_trace = traceback.format_exc().rstrip().replace("\n", " || ")
        logging.error("Error getting data for building system: %s",
                      the_trace, extra={"threadid": -1})
        shutdown(-1)


def start_threads():
    threads = []
    # we should test at least 2 threads, it's only used during testing anyway
    options.num_threads = max(options.num_threads, 2)
    for i in range(options.num_threads):
        threads.append(solverThread(i))

    for t in threads:
        t.setDaemon(True)
        t.start()


def print_to_log_local_setup():
    data = boto.utils.get_instance_metadata()
    for a, b in data.items():
        logging.info("%s -- %s", a, b, extra={"threadid": -1})


class VolumeAdderMount():
    def __init__(self):
        pass

    def add_volume(self):
        os.system("sudo mkfs.ext3 /dev/xvdb")
        os.system("sudo mkdir %s" % options.temp_space)
        os.system("sudo mount /dev/xvdb %s" % options.temp_space)

    def delete_volume(self):
        pass


class VolumeAdder():
    def __init__(self):
        self.conn = boto.ec2.connect_to_region(self._get_region())

    def _get_instance_id(self):
        instance_id = boto.utils.get_instance_metadata()
        return instance_id['instance-id']

    def _get_availability_zone(self):
        dat = boto.utils.get_instance_metadata()
        return dat["placement"]["availability-zone"]

    def _get_region(self):
        region = boto.utils.get_instance_metadata()
        return region['local-hostname'].split('.')[1]

    def add_volume(self):
        self.vol = self.conn.create_volume(50, self._get_availability_zone())
        while self.vol.status != 'available':
            print('Vol state: ', self.vol.status)
            time.sleep(5)
            self.vol.update()

        dev = "xvdc"
        logging.info("Created volume, attaching... %s", self.vol,
                     extra={"threadid": -1})
        self.conn.attach_volume(self.vol.id, self._get_instance_id(), dev)
        logging.info("Waiting for volume to show up...", extra={"threadid": -1})
        time.sleep(10)

        logging.info("Trying to mkfs, mkdir and mount", extra={"threadid": -1})
        os.system("sudo mkfs.ext3 /dev/%s" % dev)
        os.system("sudo mkdir %s" % options.temp_space)
        os.system("sudo chown ubuntu:ubuntu %s" % options.temp_space)
        os.system("sudo mount /dev/%s %s" % (dev, options.temp_space))

        return self.vol.id

    def delete_volume(self):
        try:
            os.system("sudo umount /mnt2")
            time.sleep(2)
        except:
            logging.error("Issue with unmounting, but ignored",
                          extra={"threadid": -1})

        self.conn.detach_volume(self.vol.id, force=True)
        time.sleep(1)
        self.conn.delete_volume(self.vol.id)


def parse_command_line():
    usage = "usage: %prog"
    parser = optparse.OptionParser(usage=usage, formatter=PlainHelpFormatter())
    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Be more verbose"
                      )

    parser.add_option("--host", dest="host",
                      help="Host to connect to as a client")
    parser.add_option("--port", "-p", default=10000, dest="port",
                      type="int", help="Port to use"
                      " [default: %default]",
                      )

    parser.add_option("--temp", default="/mnt2", dest="temp_space", type=str,
                      help="Temporary space to use"
                      " [default: %default]",
                      )

    parser.add_option("--noshutdown", "-n", default=False, dest="noshutdown",
                      action="store_true", help="Do not shut down"
                      )

    parser.add_option("--dir", default="/home/ubuntu/", dest="base_dir", type=str,
                      help="The home dir of cryptominisat"
                      " [default: %default]",
                      )
    parser.add_option("--net", default="ens3", dest="network_device", type=str,
                      help="The network device we will be using"
                      " [default: %default]",
                      )

    parser.add_option("--threads", dest="num_threads", type=int,
                      help="Force using this many threads")

    parser.add_option("--dev", dest="dev", type=str, default="xvdc",
                      help="Device name")

    parser.add_option("--logfile", dest="logfile_name", type=str,
                      default="python_log.log", help="Name of LOG file")

    (options, args) = parser.parse_args()

    return options, args


if __name__ == "__main__":
    global s3_bucket
    global s3_folder
    s3_bucket = "msoos-no-bucket"
    s3_folder = "no_s3_folder"
    options, args = parse_command_line()

    exitapp = False
    options.logfile_name = options.base_dir + options.logfile_name

    # get host
    if options.host is None:
        for line in boto.utils.get_instance_userdata().split("\n"):
            if "DATA" in line:
                options.host = line.split("=")[1].strip().strip('"')

        print("HOST has beeen set to %s" % options.host)

    try:
        set_up_logging()
        logging.info("Client called with parameters: %s",
                     pprint.pformat(options, indent=4).replace("\n", " || "),
                     extra={"threadid": -1})
        print_to_log_local_setup()
        v = VolumeAdderMount()
        v.add_volume()

        boto_conn = boto.connect_s3()
        update_num_threads()
        build_system_full()
        start_threads()
        while threading.active_count() > 1:
            time.sleep(0.1)

        # finish up
        logging.info("Exiting Main Thread, shutting down", extra={"threadid": -1})
        v.delete_volume()
    except:
        exc_type, exc_value, exc_traceback = sys.exc_info()
        the_trace = traceback.format_exc().rstrip().replace("\n", " || ")
        logging.error("Problem in __main__"
                      "Trace: %s", the_trace, extra={"threadid": -1})
        shutdown(-1)

    shutdown()
