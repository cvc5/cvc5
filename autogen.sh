#!/bin/sh

# Expected versions of tools.
#
# If the installed autotools aren't these versions, issue a warning
# about checking results into subversion.
libtoolize_version='libtoolize (GNU libtool) 2.2.6'
aclocal_version='aclocal (GNU automake) 1.11'
autoheader_version='autoheader (GNU Autoconf) 2.64'
autoconf_version='autoconf (GNU Autoconf) 2.64'
automake_version='automake (GNU automake) 1.11'

# first, check versions of tools

warning=
for tool in libtoolize autoheader aclocal autoconf automake; do
  version=`eval echo '${'$tool'_version}'`
  if $tool --version | grep -Fq "$version"; then :; else
    echo "WARNING: [$tool] Expected $version."
    warning=yes
  fi
done

if test -n "$warning"; then
  echo "WARNING:"
  echo "WARNING: Due to the above unexpected versions of autotools, please do not commit"
  echo "WARNING: the files these tools generate to CVC4 svn."
  echo
fi

# now do a standard autogen

set -ex

cd "$(dirname "$0")"
libtoolize --copy
aclocal -I config
autoheader -I config
touch NEWS README AUTHORS ChangeLog
touch stamp-h
autoconf -I config
automake -ac --foreign -Woverride
