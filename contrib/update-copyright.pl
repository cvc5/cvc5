#!/bin/bash

cd `dirname "$0"`/../src

cat <<EOF
Warning: this script is dangerous.  It will overwrite the header comments in your
source files to match the template in the script, attempting to retain file-specific
comments, but this isn't guaranteed.  You should run this in an svn working directory
and run "svn diff" after to ensure everything was correctly rewritten.

The directory to search for and change sources is:
  $(pwd)

Continue? y or n:
EOF

read x
if [ "$x" != 'y' -a "$x" != 'Y' -a "$x" != 'YES' -a "$x" != 'yes' ]; then
  echo Aborting operation.
  exit
fi

echo Updating sources...

for FILE in $(find . -name '*.cpp' -o -name '*.h' -o -name '*.c' -o -name '*.cc' -o -name '*.hh' -o -name '*.hpp'); do
echo $FILE

perl -i -e '\
if(m,^/\*\*\*\*\*,) {
  print "/*********************                                           -*- C++ -*-  */\n";
  print "/** (basename FILE)\n";
  print " ** This file is part of the CVC4 prototype.\n";
  print " ** Copyright (c) (date +%Y) The Analysis of Computer Systems Group (ACSys)\n";
  print " ** Courant Institute of Mathematical Sciences\n";
  print " ** New York University\n";
  print " ** See the file COPYING in the top-level source directory for licensing\n";
  print " ** information.\n";
  print " **\n";
  print " ** [[ Add file-specific comments here ]]\n";
  print " **/\n\n";
} else {
  m,^/\*\* , || exit;
  print "/*********************                                           -*- C++ -*-  */\n";
  print "/** (basename FILE)\n";
  print " ** This file is part of the CVC4 prototype.\n";
  print " ** Copyright (c) $(date +%Y) The Analysis of Computer Systems Group (ACSys)\n";
  print " ** Courant Institute of Mathematical Sciences\n";
  print " ** New York University\n";
  print " ** See the file COPYING in the top-level source directory for licensing\n";
  print " ** information.\n";
  print " **\n";
  while(<>) {
    next if !m,^ \*\* ,;
  }
}
while(<>) {
  print;
}' "$FILE"

done

