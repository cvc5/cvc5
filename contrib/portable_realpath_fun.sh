#!/bin/bash

# re-implementation of realpath, because Mac OS doesn't have realpath
# https://stackoverflow.com/questions/3572030/bash-script-absolute-path-with-os-x/18443300#18443300
portable_realpath() {
    local ourpwd=$PWD
    cd "$(dirname "$1")"
    local link=$(readlink "$(basename "$1")")
    while [ "$link" ]; do
        cd "$(dirname "$link")"
        link=$(readlink "$(basename "$1")")
    done
    local ourrealpath="$PWD/$(basename "$1")"
    cd "$ourpwd"
    echo "$ourrealpath"
}
