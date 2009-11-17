#!/usr/bin/perl -w
#
# This script goes through a source directory rewriting the top bits of
# source files to match a template (inline, below).  For files with no
# top comment, it adds a fresh one.
#
# It ignores any file/directory not starting with [a-zA-Z]
# (so, this includes . and .., vi swaps, .svn meta-info,
# .deps, etc.)
#
# It ignores any file not ending with one of:
#   .c .cc .cpp .C .h .hh .hpp .H .y .yy .ypp .Y .l .ll .lpp .L
# (so, this includes emacs ~-backups, CVS detritus, etc.)
#
# It ignores any directory matching $excluded_directories
# (so, you should add here any sources imported but not covered under
# the license.)

my $excluded_directories = '^(minisat|CVS)$';

# Years of copyright for the template.  E.g., the string
# "1985, 1987, 1992, 1997, 2008" or "2006-2009" or whatever.
my $years = '2009';

## end config ##

use strict;
use Fcntl ':mode';

my $dir = $0;
$dir =~ s,/[^/]+/*$,,;

(chdir($dir."/..") && -f "src/include/expr.h") || die "can't find top-level source directory for CVC4";
my $pwd = `pwd`; chomp $pwd;

print <<EOF;
Warning: this script is dangerous.  It will overwrite the header comments in your
source files to match the template in the script, attempting to retain file-specific
comments, but this isn't guaranteed.  You should run this in an svn working directory
and run "svn diff" after to ensure everything was correctly rewritten.

The directory to search for and change sources is:
  $pwd/src

Continue? y or n:
EOF

$_ = <STDIN>; chomp;
die 'aborting operation' if !( $_ eq 'y' || $_ eq 'yes' || $_ eq 'Y' || $_ eq 'YES' );

print "Updating sources...\n";

recurse('src');

sub recurse {
  my ($srcdir) = @_;
  opendir(my $DIR, $srcdir);
  while(my $file = readdir $DIR) {
    next if !($file =~ /^[a-zA-Z]/);

    my $mode = (stat($srcdir.'/'.$file))[2];
    my $is_directory = S_ISDIR($mode);
    if($is_directory) {
      next if $file =~ /$excluded_directories/;
      recurse($srcdir.'/'.$file);
    } else {
      next if !($file =~ /\.(c|cc|cpp|C|h|hh|hpp|H|y|yy|ypp|Y|l|ll|lpp|L)$/);
      print "$srcdir/$file...";
      my $infile = $srcdir.'/'.$file;
      my $outfile = $srcdir.'/#'.$file.'.tmp';
      open(my $IN, $infile) || die "error opening $infile for reading";
      open(my $OUT, '>', $outfile) || die "error opening $outfile for writing";
      $_ = <$IN>;
      if(m,^(%{)?/\*\*\*\*\*,) {
        print "updating\n";
        if($file =~ /\.(y|yy|ypp|Y)$/) {
          print $OUT "%{/*******************                                           -*- C++ -*-  */\n";
        } else {
          print $OUT "/*********************                                           -*- C++ -*-  */\n";
        }
        print $OUT "/** $file\n";
        print $OUT " ** This file is part of the CVC4 prototype.\n";
        print $OUT " ** Copyright (c) $years The Analysis of Computer Systems Group (ACSys)\n";
        print $OUT " ** Courant Institute of Mathematical Sciences\n";
        print $OUT " ** New York University\n";
        print $OUT " ** See the file COPYING in the top-level source directory for licensing\n";
        print $OUT " ** information.\n";
        print $OUT " **\n";
        while(my $line = <$IN>) {
          last if $line =~ /^ \*\*\s*$/;
        }
      } else {
        print "adding\n";
        if($file =~ /\.(y|yy|ypp|Y)$/) {
          print $OUT "%{/*******************                                           -*- C++ -*-  */\n";
        } else {
          print $OUT "/*********************                                           -*- C++ -*-  */\n";
        }
        print $OUT "/** $file\n";
        print $OUT " ** This file is part of the CVC4 prototype.\n";
        print $OUT " ** Copyright (c) $years The Analysis of Computer Systems Group (ACSys)\n";
        print $OUT " ** Courant Institute of Mathematical Sciences\n";
        print $OUT " ** New York University\n";
        print $OUT " ** See the file COPYING in the top-level source directory for licensing\n";
        print $OUT " ** information.\n";
        print $OUT " **\n";
        print $OUT " ** [[ Add file-specific comments here ]]\n";
        print $OUT " **/\n\n";
        if($file =~ /\.(y|yy|ypp|Y)$/) {
          while(my $line = <$IN>) {
            chomp $line;
            if($line =~ '\s*%{(.*)') {
              print $OUT "$1\n";
              last;
            }
            # just in case something's weird with the file ?
            if(!($line =~ '\s*')) {
              print $OUT "$line\n";
              last;
            }
          }
        }
      }
      while(my $line = <$IN>) {
        print $OUT $line;
      }
      close $IN;
      close $OUT;
      rename($outfile, $infile) || die "can't rename working file \`$outfile' to \`$infile'";
    }
  }
  closedir $DIR;
}

### Local Variables:
### perl-indent-level: 2
### End:
