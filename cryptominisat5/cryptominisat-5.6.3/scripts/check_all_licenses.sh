#!/usr/bin/bash
set -e
set -x

check_license_fnames() {
    #license check -- first print and then fail in case of problems
    find $1 -type f -name $2 -exec ../utils/licensecheck/licensecheck.pl -m {} \;
    NUM=$(find $1 -type f -name $2 -exec ../utils/licensecheck/licensecheck.pl -m {} \; | grep UNK | wc -l)
    shopt -s extglob
    NUM="${NUM##*( )}"
    NUM="${NUM%%*( )}"
    shopt -u extglob
    if [ "$NUM" -ne 0 ]; then
        echo "There are some files without license information!"
        exit -1
    fi
}

check_license_fnames ../tests/ CMakeLists.txt
check_license_fnames ../src/ CMakeLists.txt
check_license_fnames ../scripts/ CMakeLists.txt
