#!/usr/bin/env python
# -*- coding: utf-8 -*-

import MySQLdb as mdb
import ntpath
import subprocess
import time

con = mdb.connect('localhost', 'cmsat_presenter', '', 'cmsat');
version = "dc65769cfcba9c2bb52ee81dbea39830ad28bb1b"

with con:
    cur = con.cursor(mdb.cursors.DictCursor)
    query = """
    SELECT
    startup.runID as runid
    , startup.startTime as start
    , finishup.endTime as end
    , UNIX_TIMESTAMP(finishup.endTime)-UNIX_TIMESTAMP(startup.startTime) as diff
    , tags.tag as fname

    FROM startup, finishup, solverRun, tags

    WHERE startup.runID = solverRun.runID
    and startup.runID = tags.runID
    and startup.runID = finishup.runID
    and tagname = "filename"
    and solverRun.version = '%s'

    order by diff asc
    """ % version

    query_all = """
    SELECT
    startup.runID as runid
    , startup.startTime as start
    , tags.tag as fname

    FROM startup, solverRun, tags

    WHERE startup.runID = solverRun.runID
    and startup.runID = tags.runID
    and tagname = "filename"
    and solverRun.version = '%s'
    """ % version


    cur.execute(query_all)
    start = time.time()
    for i in range(cur.rowcount):

        row = cur.fetchone()
        #print row['diff'], row['runid'], ntpath.basename(row['fname'])
        toexec="""
        export QUERY_STRING="id=%d" ;
        php -e -r 'parse_str($_SERVER["QUERY_STRING"], $_GET); include "get_data.php";'
        """ % (row['runid'])
        into = open("dat/" + ntpath.basename(row['fname']) + ".dat", "w")
        subprocess.call(toexec, shell=True, stdout=into)
        into.close()

        print "%d/%d done %2.2f perc, %2.2f s" % (i+1, cur.rowcount, float(i+1.0)/float(cur.rowcount)*100.0, time.time()-start)
