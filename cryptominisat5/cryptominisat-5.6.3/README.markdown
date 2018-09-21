[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Linux build](https://travis-ci.org/msoos/cryptominisat.svg?branch=master)](https://travis-ci.org/msoos/cryptominisat)
[![Windows build](https://ci.appveyor.com/api/projects/status/8d000iy63xu7eau5?svg=true)](https://ci.appveyor.com/project/msoos/cryptominisat)
[![Coverity](https://scan.coverity.com/projects/507/badge.svg)](https://scan.coverity.com/projects/507)
[![code coverage](https://coveralls.io/repos/msoos/cryptominisat/badge.svg?branch=master)](https://coveralls.io/r/msoos/cryptominisat?branch=master)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/f043efa22ea64e9ba44fde0f3a4fb09f)](https://www.codacy.com/app/soos.mate/cryptominisat?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=msoos/cryptominisat&amp;utm_campaign=Badge_Grade)
[![Docker Hub](https://img.shields.io/badge/docker-latest-blue.svg)](https://hub.docker.com/r/msoos/cryptominisat/)


CryptoMiniSat SAT solver
===========================================

This system provides CryptoMiniSat, an advanced SAT solver. The system has 3
interfaces: command-line, C++ library and python. The command-line interface
takes a [cnf](http://en.wikipedia.org/wiki/Conjunctive_normal_form) as an
input in the [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html)
format with the extension of XOR clauses. The C++ interface mimics this except
that it allows for a more efficient system, with assumptions and multiple
`solve()` calls. A C compatible wrapper is also provided. The python interface provides
a high-level yet efficient API to use most of the C++ interface with ease.

When citing, always reference our [SAT 2009 conference paper](https://link.springer.com/chapter/10.1007%2F978-3-642-02777-2_24), bibtex record is [here](http://dblp.uni-trier.de/rec/bibtex/conf/sat/SoosNC09).


Docker usage
-----

To run on file `myfile.cnf`:

```
docker pull msoos/cryptominisat
cat myfile.cnf | docker run --rm -i msoos/cryptominisat
```

To run on a hand-written CNF:

```
docker pull msoos/cryptominisat
echo "1 2 0" | docker run --rm -i msoos/cryptominisat
```

To run on the file `/home/myfolder/myfile.cnf.gz` by mounting it (may be faster):

```
docker pull msoos/cryptominisat
docker run --rm -v /home/myfolder/myfile.cnf.gz:/f msoos/cryptominisat f
```

To build and run locally:

```
git clone https://github.com/msoos/cryptominisat.git
cd cryptominisat
git submodule update --init
docker build -t cms .
cat myfile.cnf | docker run --rm -i cms
```

To build and run the web interface:

```
git clone https://github.com/msoos/cryptominisat.git
cd cryptominisat
git submodule update --init
docker build -t cmsweb -f Dockerfile.web .
docker run --rm -i -p 80:80 cmsweb
```


Compiling in Linux
-----

To build and install, issue:

```
sudo apt-get install build-essential cmake
# not required but very useful
sudo apt-get install libzip-dev libboost-program-options-dev libm4ri-dev libsqlite3-dev
tar xzvf cryptominisat-version.tar.gz
cd cryptominisat-version
mkdir build && cd build
cmake ..
make
sudo make install
sudo ldconfig
```

Compiling in Mac OSX
-----

First, you must get Homebew from https://brew.sh/ then:

```
brew install cmake boost zlib
tar xzvf cryptominisat-version.tar.gz
cd cryptominisat-version
mkdir build && cd build
cmake ..
make
sudo make install
```

Compiling in Windows
-----

You will need python installed, then for Visual Studio 2015:

```
C:\> [ download cryptominisat-version.zip ]
C:\> unzip cryptominisat-version.zip
C:\> rename cryptominisat-version cms
C:\> cd cms
C:\cms> mkdir build
C:\cms> cd build

C:\cms\build> [ download http://sourceforge.net/projects/boost/files/boost/1.59.0/boost_1_59_0.zip ]
C:\cms\build> unzip boost_1_59_0.zip
C:\cms\build> mkdir boost_1_59_0_install
C:\cms\build> cd boost_1_59_0
C:\cms\build\boost_1_59_0> bootstrap.bat --with-libraries=program_options
C:\cms\build\boost_1_59_0> b2 --with-program_options address-model=64 toolset=msvc-14.0 variant=release link=static threading=multi runtime-link=static install --prefix="C:\cms\build\boost_1_59_0_install" > boost_install.out
C:\cms\build\boost_1_59_0> cd ..

C:\cms\build> git clone https://github.com/madler/zlib
C:\cms\build> cd zlib
C:\cms\build\zlib> git checkout v1.2.8
C:\cms\build\zlib> mkdir build
C:\cms\build\zlib> mkdir myinstall
C:\cms\build\zlib> cd build
C:\cms\build\zlib\build> cmake -G "Visual Studio 14 2015 Win64" -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=C:\cms\build\zlib\myinstall ..
C:\cms\build\zlib\build> msbuild /t:Build /p:Configuration=Release /p:Platform="x64" zlib.sln
C:\cms\build\zlib\build> msbuild INSTALL.vcxproj
C:\cms\build> cd ..\..

C:\cms\build> cmake -G "Visual Studio 14 2015 Win64" -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON -DZLIB_ROOT=C:\cms\build\zlib\myinstall -DBOOST_ROOT=C:\cms\build\boost_1_59_0_install ..
C:\cms\build> cmake --build --config Release .
```

You now have the static binary under `C:\cms\build\Release\cryptominisat5.exe`

Compiling under Cygwin64 in Windows
-----

This is just a rough guide, but it should work. Compiling with Visual Studio may be easier, and better, though:

```
get boost from Boost.org e.g. boost_1_66_0.tar.gz
$ tar xzvf cryptominisat-version.tar.gz
$ cd cryptominisat-version
$ mkdir build
$ cd build
$ gunzip -c ../../boost_1_66_0.tar.gz | tar -xvof -
$ cd boost_1_66_0/
$ ./bootstrap.sh --with-libraries=program_options
$ ./b2
$ export BOOST_ROOT=$(pwd)
$ cd ..
$ cmake ..
$ make
$ make install
$ cp ./boost_1_66_0/bin.v2/libs/program_options/build/gcc-gnu-6.4.0/release/threadapi-pthread/threading-multi/cygboost_program_options.dll /usr/local/bin
```

Command-line usage
-----

Let's take the file:
```
p cnf 3 3
1 0
-2 0
-1 2 3 0
```

The file has 3 variables and 3 clauses, this is reflected in the header
`p cnf 3 3` which gives the number of variables as the first number and the number of clauses as the second.
Every clause is ended by '0'. The clauses say: 1 must be True, 2
must be False, and either 1 has to be False, 2 has to be True or 3 has to be
True. The only solution to this problem is:
```
cryptominisat5 --verb 0 file.cnf
s SATISFIABLE
v 1 -2 3 0
```

Which means, that setting variable 1 True, variable 2 False and variable 3 True satisfies the set of constraints (clauses) in the CNF. If the file had contained:
```
p cnf 3 4
1 0
-2 0
-3 0
-1 2 3 0
```

Then there is no solution and the solver returns `s UNSATISFIABLE`.

Python usage
-----
The python module works with both Python 2 and Python 3. It must be compiled as per (notice "python-dev"):

```
sudo apt-get install build-essential cmake
sudo apt-get install libzip-dev libboost-program-options-dev libm4ri-dev libsqlite3-dev
sudo apt-get install python3-setuptools python3-dev
tar xzvf cryptominisat-version.tar.gz
cd cryptominisat-version
mkdir build && cd build
cmake ..
make
sudo make install
sudo ldconfig

```

You can then use it as:

```
>>> from pycryptosat import Solver
>>> s = Solver()
>>> s.add_clause([1])
>>> s.add_clause([-2])
>>> s.add_clause([3])
>>> s.add_clause([-1, 2, 3])
>>> sat, solution = s.solve()
>>> print sat
True
>>> print solution
(None, True, False, True)
```

We can also try to assume any variable values for a single solver run:
```
>>> sat, solution = s.solve([-3])
>>> print sat
False
>>> print solution
None
>>> sat, solution = s.solve()
>>> print sat
True
>>> print solution
(None, True, False, True)
```

For more detailed usage instructions, please see the README.rst under the `python`
directory.

Library usage
-----
The library uses a variable numbering scheme that starts from 0. Since 0 cannot
be negated, the class `Lit` is used as: `Lit(variable_number, is_negated)`. As
such, the 1st CNF above would become:

```
#include <cryptominisat5/cryptominisat.h>
#include <assert.h>
#include <vector>
using std::vector;
using namespace CMSat;

int main()
{
    SATSolver solver;
    vector<Lit> clause;

    //Let's use 4 threads
    solver.set_num_threads(4);

    //We need 3 variables
    solver.new_vars(3);

    //adds "1 0"
    clause.push_back(Lit(0, false));
    solver.add_clause(clause);

    //adds "-2 0"
    clause.clear();
    clause.push_back(Lit(1, true));
    solver.add_clause(clause);

    //adds "-1 2 3 0"
    clause.clear();
    clause.push_back(Lit(0, true));
    clause.push_back(Lit(1, false));
    clause.push_back(Lit(2, false));
    solver.add_clause(clause);

    lbool ret = solver.solve();
    assert(ret == l_True);
    assert(solver.get_model()[0] == l_True);
    assert(solver.get_model()[1] == l_False);
    assert(solver.get_model()[2] == l_True);
    std::cout
    << "Solution is: "
    << solver.get_model()[0]
    << ", " << solver.get_model()[1]
    << ", " << solver.get_model()[2]
    << std::endl;

    return 0;
}
```

The library usage also allows for assumptions. We can add these lines just
before the `return 0;` above:
```
vector<Lit> assumptions;
assumptions.push_back(Lit(2, true));
lbool ret = solver.solve(&assumptions);
assert(ret == l_False);

lbool ret = solver.solve();
assert(ret == l_True);
```

Since we assume that variabe 2 must be false, there is no solution. However,
if we solve again, without the assumption, we get back the original solution.
Assumptions allow us to assume certain literal values for a _specific run_ but
not all runs -- for all runs, we can simply add these assumptions as 1-long
clauses.

Multiple solutions
-----

To find multiple solutions to your problem, just run the solver in a loop
and ban the previous solution found:

```
while(true) {
    lbool ret = solver->solve();
    if (ret != l_True) {
        assert(ret == l_False);
        //All solutions found.
        exit(0);
    }

    //Use solution here. print it, for example.

    //Banning found solution
    vector<Lit> ban_solution;
    for (uint32_t var = 0; var < solver->nVars(); var++) {
        if (solver->get_model()[var] != l_Undef) {
            ban_solution.push_back(
                Lit(var, (solver->get_model()[var] == l_True)? true : false));
        }
    }
    solver->add_clause(ban_solution);
}
```

The above loop will run as long as there are solutions. It is __highly__
suggested to __only__ add into the new clause(`bad_solutions` above) the
variables that are "important" or "main" to your problem. Variables that were
only used to translate the original problem into CNF should not be added.
This way, you will not get spurious solutions that don't differ in the main,
important variables.

Preprocessor usage
-----

Run cryptominisat5 as:

```
./cryptominisat5 -p1 input.cnf simplified.cnf
some_sat_solver simplified.cnf > output
./cryptominisat5 -p2 output
```

where `some_sat_solver` is a SAT solver of your choice that outputs a solution in the format of:

```
s SATISFIABLE
v [solution] 0
```

or 

```
s UNSATISFIABLE
```

You can tune the schedule of simplifications by issuing `--sched "X,Y,Z..."`. The default schedule for preprocessing is:

```
handle-comps,scc-vrepl, cache-clean, cache-tryboth,sub-impl, intree-probe, probe,
sub-str-cls-with-bin, distill-cls, scc-vrepl, sub-impl,occ-backw-sub-str,
occ-xor, occ-clean-implicit, occ-bve, occ-bva, occ-gates,str-impl, cache-clean,
sub-str-cls-with-bin, distill-cls, scc-vrepl, sub-impl,str-impl, sub-impl,
sub-str-cls-with-bin, occ-backw-sub-str, occ-bve,check-cache-size, renumber
```

It is a good idea to put `renumber` as late as possible, as it renumbers the variables for memory usage reduction.

Gaussian elimination
-----
For building with Gaussian Elimination, you need to build as per:

```
sudo apt-get install build-essential cmake
sudo apt-get install libzip-dev libboost-program-options-dev libm4ri-dev libsqlite3-dev
tar xzvf cryptominisat-version.tar.gz
cd cryptominisat-version
mkdir build && cd build
cmake -DUSE_GAUSS=ON ..
make
sudo make install
```

To use Gaussian elimination, provide a CNF with xors in it (either in CNF or XOR+CNF form) and tune the gaussian parameters. Use `--hhelp` to find all the gaussian elimination options:

```
Gauss options:
  --iterreduce arg (=1)       Reduce iteratively the matrix that is updated.We
                              effectively are moving the start to the last
                              column updated
  --maxmatrixrows arg (=3000) Set maximum no. of rows for gaussian matrix. Too
                              large matrixes should be discarded for reasons of
                              efficiency
  --autodisablegauss arg (=1) Automatically disable gauss when performing badly
  --minmatrixrows arg (=5)    Set minimum no. of rows for gaussian matrix.
                              Normally, too small matrixes are discarded for
                              reasons of efficiency
  --savematrix arg (=2)       Save matrix every Nth decision level
  --maxnummatrixes arg (=3)   Maximum number of matrixes to treat.
```

If any of these options seem to be non-existent, then either you forgot to compile the SAT solver with the above options, or you forgot to re-install it with `sudo make install`.

Testing
-----
For testing you will need the GIT checkout and build as per:

```
sudo apt-get install build-essential cmake git
sudo apt-get install libzip-dev libboost-program-options-dev libm4ri-dev libsqlite3-dev
sudo apt-get install git python3-pip python3-setuptools python3-dev
sudo pip3 install --upgrade pip
sudo pip3 install lit
git clone https://github.com/msoos/cryptominisat.git
cd cryptominisat
git submodule update --init
mkdir build && cd build
cmake -DENABLE_TESTING=ON ..
make -j4
make test
sudo make install
sudo ldconfig
```

Fuzzing
-----
Build for test as per above, then:

```
cd ../cryptominisat/scripts/fuzz/
./fuzz_test.py
```

Configuring a build for a minimal binary&library
-----
The following configures the system to build a bare minimal binary&library. It needs a compiler, but nothing much else:

```
cmake -DONLY_SIMPLE=ON -DNOZLIB=ON -DNOM4RI=ON -DSTATS=OFF -DNOVALGRIND=ON -DENABLE_TESTING=OFF .
```

Trying different configurations
-----
Try solving using different reconfiguration values between 1..15 as per:

```
./cryptominisat5 --reconfat 0 --reconf 1 my_hard_problem.cnf
./cryptominisat5 --reconfat 0 --reconf 2 my_hard_problem.cnf
...
./cryptominisat5 --reconfat 0 --reconf 15 my_hard_problem.cnf
```

These configurations are designed to be relatively orthogonal. Check if any of them solve a lot faster. If it does, try using that for similar problems going forward. Please do come back to the author with what you have found to work best for you.

Getting learnt clauses
-----
As an experimental feature, you can get the learnt clauses from the system with the following code, where `lits` is filled with learnt clauses every time `get_next_small_clause` is called. The example below will eventually return all clauses of size 4 or less. You can call `end_getting_small_clauses` at any time.

```
SATSolver s;
//fill the solver, run solve, etc.

//Get all clauses of size 4 or less

s->start_getting_small_clauses(4);

vector<Lit> lits;
bool ret = true;
while (ret) {
    bool ret = s->get_next_small_clause(lits);
    if (ret) {
        //deal with clause in "lits"
        add_to_my_db(lits);
    }
}
s->end_getting_small_clauses();
```

C usage
-----
See src/cryptominisat_c.h.in for details. This is an experimental feature.
