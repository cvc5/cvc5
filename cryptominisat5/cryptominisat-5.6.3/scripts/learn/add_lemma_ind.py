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


class Query:
    def __init__(self, dbfname):
        self.conn = sqlite3.connect(dbfname)
        self.c = self.conn.cursor()
        self.runID = self.find_runID()
        # zero out goodClauses
        self.c.execute('delete from goodClauses;')
        self.cur_good_ids_num = 0
        self.num_goods_total = 0
        self.cur_good_ids = []

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.conn.commit()
        self.conn.close()

    def parse_and_add_lemmas(self, lemmafname):
        with open(lemmafname, "r") as f:
            for line in f:
                line = line.strip().split(" ")
                self.parse_one_line(line)

        # final dump
        self.dump_ids()

        print("Parsed %d number of good lemmas" % self.num_goods_total)

    def parse_one_line(self, line):
        self.cur_good_ids_num += 1
        self.num_goods_total += 1

        # get ID
        myid = int(line[0])
        assert myid >= 0, "ID is always at least 0"
        assert myid != 0, "ID with 0 should not even be printed"

        num_used = int(line[1])
        last_used = int(line[2])

        # append to cur_good_ids
        self.cur_good_ids.append((self.runID, myid, num_used, last_used))

        # don't run out of memory, dump early
        if self.cur_good_ids_num > 10000:
            self.dump_ids()

    def dump_ids(self):
        self.c.executemany("""
        INSERT INTO goodClauses (`runID`, `clauseID`, `num_used`, `last_confl_used`)
        VALUES (?, ?, ?, ?);""", self.cur_good_ids)
        self.cur_good_ids = []
        self.cur_good_ids_num = 0

    def find_runID(self):
        q = """
        SELECT runID
        FROM startUp
        order by startTime desc
        """

        runID = None
        for row in self.c.execute(q):
            if runID is not None:
                print("ERROR: More than one RUN in the SQL, can't add lemmas!")
                exit(-1)
            runID = int(row[0])

        print("runID: %d" % runID)
        return runID


if __name__ == "__main__":
    usage = """usage: %prog [options] sqlite_db lemmas

It adds lemma indices from "lemmas" to the SQLite database, indicating whether
it was good or not."""

    parser = optparse.OptionParser(usage=usage)

    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")

    (options, args) = parser.parse_args()

    if len(args) != 2:
        print("Error. Please follow usage")
        print(usage)
        exit(-1)

    dbfname = args[0]
    lemmafname = args[1]
    print("Using sqlite3db file %s" % dbfname)
    print("Using lemma file %s" % lemmafname)

    with Query(dbfname) as q:
        q.parse_and_add_lemmas(lemmafname)

    print("Finished adding good lemma indicators to db %s" % dbfname)
    exit(0)
