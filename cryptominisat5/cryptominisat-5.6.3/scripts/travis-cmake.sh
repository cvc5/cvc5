#!/bin/bash

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

# This file wraps CMake invocation for TravisCI
# so we can set different configurations via environment variables.

set -e
set -x

# fix TravisCI issue --> https://github.com/travis-ci/travis-ci/issues/8920
python -c "import fcntl; fcntl.fcntl(1, fcntl.F_SETFL, 0)"

check_license() {
    #license check -- first print and then fail in case of problems
    ./utils/licensecheck/licensecheck.pl -m  $1
    NUM=$(./utils/licensecheck/licensecheck.pl -m  $1 | grep UNK | wc -l)
    shopt -s extglob
    NUM="${NUM##*( )}"
    NUM="${NUM%%*( )}"
    shopt -u extglob
    if [ "$NUM" -ne 0 ]; then
        echo "There are some files without license information!"
        exit -1
    fi
}

check_license_fnames() {
    #license check -- first print and then fail in case of problems
    find $1 -type f -name $2 -exec utils/licensecheck/licensecheck.pl -m {} \;
    NUM=$(find $1 -type f -name $2 -exec utils/licensecheck/licensecheck.pl -m {} \; | grep UNK | wc -l)
    shopt -s extglob
    NUM="${NUM##*( )}"
    NUM="${NUM%%*( )}"
    shopt -u extglob
    if [ "$NUM" -ne 0 ]; then
        echo "There are some files without license information!"
        exit -1
    fi
}

check_license CMakeLists.txt
check_license ./src
check_license ./tests/
check_license ./scripts/fuzz/
check_license ./scripts/learn/
check_license ./scripts/aws/

check_license_fnames tests/ CMakeLists.txt
check_license_fnames src/ CMakeLists.txt
check_license_fnames scripts/ CMakeLists.txt

NUM=$(./utils/licensecheck/licensecheck.pl -m  ./tests | grep UNK | wc -l)
shopt -s extglob
NUM="${NUM##*( )}"
NUM="${NUM%%*( )}"
shopt -u extglob
if [ "$NUM" -ne 0 ]; then
    echo "There are some files without license information!"
    exit -1
fi

set -x

SOURCE_DIR=$(pwd)
cd build
BUILD_DIR=$(pwd)

# Note eval is needed so COMMON_CMAKE_ARGS is expanded properly


# for OSX keep prefix
PATH_PREFIX_ADD=""
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
    PATH_PREFIX_ADD="-DCMAKE_INSTALL_PREFIX=/usr"
fi

case $CMS_CONFIG in
    SLOW_DEBUG)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DSLOW_DEBUG:BOOL=ON \
                   ${PATH_PREFIX_ADD} \
                   "${SOURCE_DIR}"
    ;;

    NORMAL)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   ${PATH_PREFIX_ADD} \
                   "${SOURCE_DIR}"
    ;;

    NORMAL_PYTHON2)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DFORCE_PYTHON2=ON -DENABLE_TESTING:BOOL=ON \
                   ${PATH_PREFIX_ADD} \
                   "${SOURCE_DIR}"
    ;;

    LARGEMEM)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DLARGEMEM:BOOL=ON \
                   ${PATH_PREFIX_ADD} \
                   "${SOURCE_DIR}"
    ;;

    LARGEMEM_GAUSS)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DLARGEMEM:BOOL=ON \
                   -DUSE_GAUSS=ON \
                   "${SOURCE_DIR}"
    ;;

    COVERAGE)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DCOVERAGE:BOOL=ON \
                   -DUSE_GAUSS=ON \
                   -DSTATS:BOOL=ON \
                   -DSLOW_DEBUG:BOOL=ON \
                   -DSTATICCOMPILE:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    STATIC)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DSTATICCOMPILE:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    ONLY_SIMPLE)
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DONLY_SIMPLE:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    ONLY_SIMPLE_STATIC)
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DONLY_SIMPLE:BOOL=ON \
                   -DSTATICCOMPILE:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    STATS)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DSTATS:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    NOZLIB)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DNOZLIB:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    RELEASE)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DCMAKE_BUILD_TYPE:STRING=Release \
                   "${SOURCE_DIR}"
    ;;

    NOSQLITE)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get remove libsqlite3-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;


    NOPYTHON)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get remove -y python3-dev python2.7-dev python-dev libpython-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    INTREE_BUILD)
        cd ..
        SOURCE_DIR=$(pwd)
        BUILD_DIR=$(pwd)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake -DENABLE_TESTING:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    WEB)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi

        cd "$SOURCE_DIR"
        #./cmsat_mysql_setup.sh
        cd "$BUILD_DIR"

        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DSTATS:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    SQLITE)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libsqlite3-dev; fi

        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DSTATS:BOOL=ON \
                   "${SOURCE_DIR}"
    ;;

    NOTEST)
        rm -rf ${SOURCE_DIR}/utils/gtest
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        eval cmake "${SOURCE_DIR}"
    ;;

    GAUSS)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libsqlite3-dev; fi

        eval cmake -DENABLE_TESTING:BOOL=ON \
                   -DUSE_GAUSS=ON \
                   ${PATH_PREFIX_ADD} \
                   "${SOURCE_DIR}"
    ;;

    M4RI)
        if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then sudo apt-get install libboost-program-options-dev; fi
        wget https://bitbucket.org/malb/m4ri/downloads/m4ri-20140914.tar.gz
        tar xzvf m4ri-20140914.tar.gz
        cd m4ri-20140914/
        ./configure
        make
        sudo make install
        cd ..

        eval cmake -DENABLE_TESTING:BOOL=ON \
            "${SOURCE_DIR}"
    ;;

    *)
        echo "\"${CMS_CONFIG}\" configuration not recognised"
        exit 1
    ;;
esac

make -j2 VERBOSE=1

if [ "$CMS_CONFIG" == "NOTEST" ]; then
    sudo make install VERBOSE=1
    exit 0
fi

echo $(ls lib)
echo $(ls pycryptosat)
echo $(otool -L pycryptosat/pycryptosat.so)
echo $(ldd      pycryptosat/pycryptosat.so)
echo $(otool -L lib/libcryptominisat5.so.5.0)
echo $(ldd      lib/libcryptominisat5.so.5.0)

if [ "$CMS_CONFIG" = "ONLY_SIMPLE_STATIC" ] || [ "$CMS_CONFIG" = "STATIC" ] ; then
    if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
        echo $(ldd ./cryptominisat5_simple)
        ldd ./cryptominisat5_simple  | grep "not a dynamic";
    fi

    if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
        echo $(otool -L ./cryptominisat5_simple)
        ! (otool -L ./cryptominisat5_simple  | grep "libcryptominisat");
        ! (otool -L ./cryptominisat5_simple  | grep "libz");
        ! (otool -L ./cryptominisat5_simple  | grep "libboost");
    fi
fi

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then echo $(ldd      ./cryptominisat5); fi
if [[ "$TRAVIS_OS_NAME" == "osx"   ]]; then echo $(otool -L ./cryptominisat5); fi
if [ "$CMS_CONFIG" = "STATIC" ] ; then
    if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
        echo $(ldd ./cryptominisat5)
        ldd ./cryptominisat5  | grep "not a dynamic";
    fi

    if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
        echo $(otool -L ./cryptominisat5)
        ! (otool -L ./cryptominisat5  | grep "libcryptominisat");
        ! (otool -L ./cryptominisat5  | grep "libz");
        ! (otool -L ./cryptominisat5  | grep "libboost");
    fi
fi

ctest -V
sudo make install VERBOSE=1
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
    echo $(sudo ldconfig)
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib
fi


##################
# setting up python environment
##################

which python
python --version
echo $PYTHONPATH
if [ "$CMS_CONFIG" == "NORMAL_PYTHON2" ]; then
    export MYPYTHON=python2
else
    export MYPYTHON=python3
fi
echo "MYPYTHON is '${MYPYTHON}'"
which ${MYPYTHON}

if [[ "$CMS_CONFIG" == "NORMAL" ]] || [[ "$CMS_CONFIG" == "NORMAL_PYTHON2" ]] || [[ "$CMS_CONFIG" == "SLOW_DEBUG" ]] || [[ "$CMS_CONFIG" == "LARGEMEM" ]] || [[ "$CMS_CONFIG" == "GAUSS" ]] ; then
    echo "from __future__ import print_function
import sys
print(sys.path)
" > check_path.py
    ${MYPYTHON} check_path.py
    echo $PYTHONPATH
    export PYTHONPATH=$PYTHONPATH:/usr/lib/python3.4/site-packages
    export PYTHONPATH=$PYTHONPATH:/usr/lib/python2.7/site-packages
    echo $PYTHONPATH
    ${MYPYTHON} check_path.py

    (
    cd pycryptosat/tests/
    ${MYPYTHON} test_pycryptosat.py
    )
fi

case $CMS_CONFIG in
    WEB)
        echo "1 2 0" | ./cryptominisat5 --sql 1 --zero-exit-status
    ;;

    SQLITE)
        echo "1 2 0" | ./cryptominisat5 --sql 2 --zero-exit-status
    ;;

    M4RI)
        echo "1 2 0" | ./cryptominisat5 --xor 1 --zero-exit-status
    ;;

    *)
        echo "\"${CMS_CONFIG}\" Binary no extra testing (sql, xor, etc), skipping this part"
    ;;
esac

if [ "$CMS_CONFIG" == "NORMAL" ] ; then
    (
    cd
    ${MYPYTHON} -c "
import pycryptosat
a = pycryptosat.Solver()
a.add_clause([1,2,3])
print(a.solve())"
    )
fi



# elimination checks
# NOTE: minisat doesn't build with clang
if [ "$CMS_CONFIG" == "NORMAL" ] && [ "$CXX" != "clang++" ] ; then
    CMS_PATH="${BUILD_DIR}/cryptominisat5"

    # building STP
    cd "${BUILD_DIR}"
    # minisat
    git clone --depth 1 https://github.com/niklasso/minisat.git
    cd minisat
    mkdir -p build
    cd build
    cmake ..
    make -j2
    sudo make install VERBOSE=1
    cd "${BUILD_DIR}"

    # STP
    cd "${BUILD_DIR}"
    git clone --depth 1 https://github.com/stp/stp.git
    cd stp
    mkdir -p build
    cd build
    cmake ..
    make -j2
    sudo make install VERBOSE=1
    cd "${BUILD_DIR}"
fi


#do fuzz testing
if [ "$CMS_CONFIG" != "ONLY_SIMPLE" ] && [ "$CMS_CONFIG" != "ONLY_SIMPLE_STATIC" ] && [ "$CMS_CONFIG" != "WEB" ] && [ "$CMS_CONFIG" != "NOPYTHON" ] && [ "$CMS_CONFIG" != "COVERAGE" ] && [ "$CMS_CONFIG" != "INTREE_BUILD" ] && [ "$CMS_CONFIG" != "STATS" ] && [ "$CMS_CONFIG" != "SQLITE" ] ; then
    cd ../scripts/fuzz/
    which ${MYPYTHON}
    ${MYPYTHON} ./fuzz_test.py --novalgrind --small --fuzzlim 30
fi

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
    case $CMS_CONFIG in
    WEB)
        #we are now in the main dir, ./src dir is here
        cd ..
        pwd

        cd web
        sudo apt-get install python-software-properties
        sudo add-apt-repository -y ppa:chris-lea/node.js
        sudo apt-get update
        sudo apt-get install -y nodejs
        ./install_web.sh
    ;;

    STATS)
        ln -s ../scripts/build_scripts/* .
        ln -s ../scripts/learn/* .
        # ./test_id.sh
        sudo apt-get install -y --force-yes graphviz
        # sudo apt-get install -y --force-yes blas
        # sudo pip3 install numpy
        # sudo pip3 install scipy
        # sudo pip3 install sklearn
        # sudo pip3 install pandas
        # ./test_predict.sh
    ;;

    COVERAGE)
        #we are now in the main dir, ./src dir is here
        cd ..
        pwd

        # capture coverage info
        lcov --directory build/cmsat5-src/CMakeFiles/libcryptominisat5.dir --capture --output-file coverage.info

        # filter out system and test code
        lcov --remove coverage.info 'tests/*' '/usr/*' 'scripts/*' 'utils/*'--output-file coverage.info

        # debug before upload
        lcov --list coverage.info

        # only attempt upload if $COVERTOKEN is set
        if [ -n "$COVERTOKEN" ]; then
            coveralls-lcov --repo-token "$COVERTOKEN" coverage.info # uploads to coveralls
        fi
    ;;

    *)
        echo "\"${CMS_CONFIG}\" No further testing"
    ;;
    esac
fi

