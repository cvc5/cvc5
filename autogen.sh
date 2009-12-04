#!/bin/sh -ex

cd "$(dirname "$0")"
libtoolize --copy
autoheader -I config
touch NEWS README AUTHORS ChangeLog
touch stamp-h
aclocal -I config
autoconf -I config
automake -ac --foreign -Woverride
