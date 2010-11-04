

stat_name_delim = ","

class Database:
    def __init__(self):
        self.rows = []
        self.currentRow = dict()
    def insert(self, name, val):
        assert name not in self.currentRow
        self.currentRow[name] = val
    def commitRow(self):
        self.rows.append(self.currentRow)
        self.currentRow = dict()
    def currentRowIsClear(self):
        return len(self.currentRow) == 0
    def writeDB(self, file, order):
        assert self.currentRowIsClear()
        first = True
        for name in order:
            if first:
                first = False
            else:
                file.write(",")
            file.write(name)

        file.write("\n")
        for row in self.rows:
            first = True
            for name in order:
                if first:
                    first = False
                else:
                    file.write(",")
                if name in row:
                    file.write(str(row[name]))
                else:
                    file.write(" ")
            file.write("\n")

def readDatabase(filename):
    file = open(filename)
    db = Database()
    first = True
    names = []
    for line in file:
        if first:
            first = False
            (_,hash,line) = line.partition("#")
            assert hash == "#"
            line = line.strip()
            names = line.split(",")
            for n in names:
                assert n in registry
        else:
            vals = line.split(",")
            for index in xrange(len(vals)):
                addStat(db,names[index],vals[index])
            db.commitRow()
    file.close()
    return db


int_default = "-1"
def str2int(x):
    if x.strip() == "":
        return int_default
    else:
        return int(x)

str2str = lambda x: x

str2strip2str = lambda x: x.strip()

float_default = "-1.0"
def str2float(x):
    if x.strip() == "":
        return float_default
    else:
        return float(x)

def strpercent2float(x):
    if x.strip() == "":
        return float_default
    else:
        return float(x.strip('%'))

registry = dict()
registry["sat/unsat"] = lambda x: x.upper() == "SAT" and 1 or 0
registry["filename"] = str2strip2str
registry["sat::clauses_literals"] = str2int
registry["sat::tot_literals"] = str2int
registry["sat::starts"] = str2int
registry["sat::rnd_decisions"] = str2int
registry["sat::propagations"] = str2int
registry["sat::max_literals"] = str2int
registry["sat::learnts_literals"] = str2int
registry["sat::decisions"] = str2int
registry["sat::conflicts"] = str2int
registry["theory::arith::AssertLowerConflicts"] = str2int
registry["theory::arith::AssertUpperConflicts"] = str2int
registry["theory::arith::UpdateConflicts"] = str2int
registry["theory::arith::Average#ConstantInPivotRow"] = str2float
registry["theory::arith::AveragePivotLength"] = str2float

registry["theory::arith::Ejections"] = str2int
registry["theory::arith::UnEjections"] = str2int

registry["theory::arith::SlackVariables"] = str2int
registry["theory::arith::UserVariables"] = str2int

registry["theory::arith::pivots"] = str2int
registry["theory::arith::updates"] = str2int
registry["theory::aug_lemma"] = str2int
registry["theory::conflicts"] = str2int
registry["theory::explanation"] = str2int
registry["theory::lemma"] = str2int
registry["theory::propagate"] = str2int

registry["cpu_percent"] = strpercent2float
registry["exit_status"] = str2int
registry["system_time"] = str2float
registry["user_time"] = str2float
registry["major_page_faults"] = str2float
registry["minor_page_faults"] = str2int
registry["average_unshared_memory"] = str2int
registry["average_total_memory"] = str2int
registry["maximum_resident_size"] = str2int
registry["average_resident_size"] = str2int

registry["id"] = str2int

def find(l, elem):
    for i in xrange(len(l)):
        if elem == l[i]:
            return i
    return -1

def pushToFront(l, elem):
    l.remove(elem)
    l.insert(0,elem)

regOrder = list(registry.keys())
regOrder.sort()
pushToFront(regOrder, "filename")
pushToFront(regOrder, "theory::propagate")
pushToFront(regOrder, "theory::conflicts")
pushToFront(regOrder, "sat::decisions")
pushToFront(regOrder, "system_time")
pushToFront(regOrder, "user_time")

def isSatResult(line):
    up = line.upper().strip()
    if up == "UNSAT":
        return True
    elif up  == "SAT":
        return True
    else:
        return False

def addStat(db, name, result):
    assert name in registry
    interpreter = registry[name]

    val = interpreter(result)
    db.insert(name, val)

def handleCoutFile(db, filename):
    file = open(filename)
    num_lines = 0
    for line in file:
        assert num_lines <= 2
        num_lines += 1
        if(isSatResult(line)):
            continue
        time_return = line.split()
        # First word is 'empty' to distinguish the 'empty' output
        addStat(db, "exit_status", time_return[1])
        addStat(db, "system_time", time_return[2])
        addStat(db, "user_time", time_return[3])
        addStat(db, "cpu_percent", time_return[4])
        addStat(db, "major_page_faults", time_return[5])
        addStat(db, "minor_page_faults", time_return[6])
        addStat(db, "average_unshared_memory", time_return[7])
        addStat(db, "average_total_memory", time_return[8])
        addStat(db, "maximum_resident_size", time_return[9])
        addStat(db, "average_resident_size", time_return[10])
    file.close()

ignoreThese = ["Illegal instruction",
               "Aborted",
               "CVC4 interrupted by timeout.",
               "CVC4 suffered a segfault.",
               "ssh: Could not resolve hostname",
               "Trace/breakpoint trap",
               "Segmentation fault"]
def ignoreFault(ln):
    for ignore in ignoreThese:
        if (ln.find(ignore) != -1):
            return True
    return False


def handleLine(db, ln):
    assert ln.strip() != ""
    if isSatResult(ln):
        addStat(db,"sat/unsat",ln)
    elif (not ignoreFault(ln)):
        (name,delim,result) = ln.partition(stat_name_delim)
        assert delim != ""
        addStat(db, name,result)

def handleCerrFile(db, filename):
    assert db.currentRowIsClear()
    file = open(filename)
    for line in file:
        handleLine(db,line)
    file.close()

ignore_files = ["done", "done.err", "init", "init.err"]

import os
def handleDirectory(db, path):
    files = os.listdir(path)
    for name in files:
        if name in ignore_files:
            continue
        if(not name.endswith(".err")):
            errFile = name+".err"
            handleCerrFile(db, path+'/'+errFile)
            addStat(db, "id", name)
            handleCoutFile(db, path+'/'+name)
            db.commitRow()

import sys

dbfile = sys.argv[1]
target = sys.argv[2]

assert os.path.exists(dbfile)
assert os.path.exists(target)

db = readDatabase(dbfile)

if os.path.isdir(target):
    handleDirectory(db, target)
else:
    handleFile(db, target)
    db.commitRow()

db.writeDB(sys.stdout, regOrder)
