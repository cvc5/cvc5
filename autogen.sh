#!/bin/sh -ex

cd "$(dirname "$0")"
mkdir -p m4
libtoolize --copy
autoheader -I m4
touch NEWS README AUTHORS ChangeLog
touch stamp-h
aclocal -I m4
autoconf -I m4
automake -ac --foreign
