#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function
import sqlite3
import optparse
import operator


class Query:
    def __init__(self):
        self.conn = sqlite3.connect(dbfname)
        self.c = self.conn.cursor()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.conn.close()

    def find_time_outliers(self):
        print("----------- TIME OUTLIERS --------------")
        query = """
        select tags.tag, name, elapsed
        from timepassed,tags
        where name != 'search' and elapsed > %d and
        tags.tagname="filename" and tags.runID = timepassed.runID
        order by elapsed desc;
        """ % (options.maxtime)

        for row in self.c.execute(query):
            operation = row[1]
            t = row[2]
            fname = self.get_fname(row[0])
            print("%-32s    %-20s   %.1fs" % (fname, operation, t))

    def check_memory(self):
        print("----------- MEMORY OUTLIERS --------------")

        query = """
        select tags.tag, memused.name, max(memused.MB)
        from memused,tags
        where  tags.tagname="filename"
        and tags.runID = memused.runID
        and memused.MB > %d
        and memused.name != 'vm'
        and memused.name != 'rss'
        and memused.name != 'longclauses'
        group by tags.tag, memused.name
        order by MB desc;
        """ % (options.maxmemory)

        for row in self.c.execute(query):
            subsystem = row[1]
            gigs = row[2]/1000.0
            fname = self.get_fname(row[0])
            print("%-32s    %-20s   %.1f GB" % (fname, subsystem, gigs))

    def check_memory_rss(self):
        print("----------- MEMORY OUTLIERS RSS --------------")

        query = """
        select tags.tag, memused.name, max(memused.MB)
        from memused,tags
        where  tags.tagname="filename"
        and tags.runID = memused.runID
        and memused.MB > %d
        and memused.name == 'rss'
        group by tags.tag, memused.name
        order by MB desc;
        """ % (options.maxmemory*2)

        for row in self.c.execute(query):
            subsystem = row[1]
            gigs = row[2]/1000.0
            fname = self.get_fname(row[0])
            print("%-32s    %-20s   %.1f GB" % (fname, subsystem, gigs))

    def find_worst_unaccounted_memory(self):
        print("----------- Largest RSS vs counted differences --------------")
        query = """
        select tags.tag, a.`runtime`, abs((b.rss-a.mysum)/b.rss) as differperc,
            a.mysum as counted, b.rss as total
        from tags,

        (select runID, `runtime`, sum(MB) as mysum
        from memused
        where name != 'rss'
        and name != 'vm'
        group by `runtime`, runID) as a,

        (select runID, name, `runtime`, MB as rss
        from memused
        where name = 'rss') as b

        where tags.runID = a.runID
        and tags.tagname="filename"
        and a.runID = b.runID
        and a.`runtime` = b.`runtime`
        and total > %d

        order by differperc desc
        """ % (options.minmemory)

        for row,_ in zip(self.c.execute(query), range(10)):
            t = row[1]
            diff_perc = row[2]
            counted = row[3]
            total = row[4]
            fname = self.get_fname(row[0])
            print("%-32s    at: %-8.1fs   counted: %3.2f GB   rss: %3.2f GB" % (fname, t, counted/1000.0, total/1000.0))

    def memory_distrib(self):
        print("----------- MEMORY DISTRIBUTION --------------")
        print("all divided by RSS -- resident size")

        query = """
        select sum(MB)
        from memused
        where name != 'vm'
        and name != 'rss';
        """
        for row in self.c.execute(query):
            recorded_mem = float(row[0])

        query = """
        select sum(MB)
        from memused
        where name = 'rss';
        """
        for row in self.c.execute(query):
            rss_mem = float(row[0])

        unaccounted = rss_mem - recorded_mem;
        print("%-20s   %.1f%%" % ("unaccounted", unaccounted/rss_mem*100.0))

        query = """
        select name, sum(MB) as memsum
        from memused
        where name != 'vm'
        and name != 'rss'
        group by name
        order by memsum desc;
        """

        for row in self.c.execute(query):
            subsystem = row[0]
            mbs = float(row[1])
            print("%-20s   %.1f%%" % (subsystem, mbs/rss_mem*100.0))

    def get_fname(self, val) :
        fname = val.split("/")
        fname = fname[len(fname)-1]
        fname = fname.rstrip(".cnf.gz")
        #if len(fname) > 40:
        #    fname = fname[:30] + "..." + fname[len(fname)-10:]

        return fname

    def calc_time_spent(self):
        print("----------- TIME DISTRIBUTION --------------")

        query = """
        select sum(elapsed)
        from timepassed
        where name='search';
        """
        for row in self.c.execute(query):
            search_time = float(row[0])

        query = """
        select sum(elapsed)
        from timepassed
        where name!='search';
        """
        for row in self.c.execute(query):
            other_time = float(row[0])

        total = search_time + other_time
        print("Total: %10.1fh Search: %3.1f%%, Other: %3.1f%%" %
              (total/3600, search_time/total*100, other_time/total*100))

        query = """
        select name, sum(elapsed)
        from timepassed
        group by name;
        """
        times = {}
        for row in self.c.execute(query):
            times[row[0]] = float(row[1])

        # print("Names: %s" % times)
        sorted_t = sorted(times.items(), key=operator.itemgetter(1), reverse=True)
        for (name, t) in sorted_t:
            name = name[:40]
            print("%-40s   %3.1f%%" % (name, t/total*100))

    def find_intersting_problems(self):
        print("----------- Interesting problems for learning --------------")

        #Find CNFs that are interesting:
        #* solved in under 500s
        #* UNSAT
        #* more conflicts than 60'000

        #last conflict > 60000, UNSAT, solvetime under 500s
        query = """
        select a.runID, tags.tag, a.maxtime, a.maxconfl, mems.maxmem from

            (select runID, max(conflicts) as maxconfl, max(`runtime`) as maxtime
            from timepassed
            group by runID
            ) as a,
            (select runID
            from finishup
            where status = "l_False"
            ) as b,
            (select runID, max(MB) as maxmem
            from memused
            group by runID
            ) as mems, tags

            where a.maxconfl > 20000
            and a.maxconfl < 400000
            and a.maxtime < 400
            and a.maxtime > 10
            and a.runID = b.runID
            and tags.runID = a.runID
            and tags.tagname = "filename"
            and mems.runID = a.runID
            order by maxtime desc
        """

        runIDs = []
        for row in self.c.execute(query):
            fname = row[1].split("/")
            fname = fname[len(fname)-1]
            runID = int(row[0])
            t = row[2]
            confl = row[3]
            mb = row[4]
            print("runID %-10d  t(mins): %-6.1f  confl(K): %-6.1f  mem(GB): %-6.1f  fname: %s" %
                  (runID, t/60.0, confl/(1000.0), mb/1024.0, fname))


if __name__ == "__main__":
    usage = "usage: %prog [options] sqlitedb"
    parser = optparse.OptionParser(usage=usage)

    parser.add_option("--maxtime", metavar="CUTOFF",
                      dest="maxtime", default=20, type=int,
                      help="Max time for an operation")

    parser.add_option("--maxmemory", metavar="CUTOFF",
                      dest="maxmemory", default=500, type=int,
                      help="Max memory for a subsystem")

    parser.add_option("--minmemory", metavar="MINMEM",
                      dest="minmemory", default=800, type=int,
                      help="Minimum memory to be checked for RSS vs counted check")

    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")

    (options, args) = parser.parse_args()

    if len(args) != 1:
        print("ERROR: You must give exactly one argument, the sqlite3 database file")
        exit(-1)

    dbfname = args[0]
    print("Using sqlite3db file %s" % dbfname)

    #peform queries
    with Query() as q:
        q.find_intersting_problems()
        q.find_worst_unaccounted_memory()
        q.check_memory_rss()
        q.check_memory()
        q.memory_distrib()
        q.find_time_outliers()
        q.calc_time_spent()



#select timepassed.runID, tag,elapsed from timepassed,tags where name like 'shorten and str red%' and elapsed > 2 and tags.runID = timepassed.runID;

#select * from timepassed where elapsed > 20 and name not like 'search';

#select * from startup, solverRun, finishup where finishup.runID = solverRun.runID and (finishup.endTime - startup.startTime) < 30 and solverRun.version = "618b5e79fdd8a15918e19fb76ca08aa069f14b54" and solverRun.runID = startup.runID;
