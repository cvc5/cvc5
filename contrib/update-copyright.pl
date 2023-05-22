#!/usr/bin/perl -w
#
# update-copyright.pl
# Copyright (c) 2009-2023  The cvc5 Project
#
# usage: update-copyright [-m] [files/directories...]
#        update-copyright [-h | --help]
#
# This script goes through a source directory rewriting the top bits of
# source files to match a template (inline, below).  For files with no
# top comment, it adds a fresh one.
#
# if no files/directories are unspecified, the script scans its own
# parent directory's "src" directory.  Since it lives in contrib/ in
# the cvc5 source tree, that means src/ in the cvc5 source tree.
#
# If -m is specified as the first argument, all files and directories
# are scanned, but only ones modified in the index or working tree
# are modified (i.e., those that have at least one status M in
# "git status -s").
#
# It ignores any file/directory not starting with [a-zA-Z]
# (so, this includes . and .., vi swaps, .git meta-info,
# .deps, etc.)
#
# It ignores any file not ending with one of:
#   .c .cc .cpp .h .hh .hpp .g .py .cmake .cmake.in CMakeLists.txt
#   [ or those with ".in" also suffixed, e.g., .cpp.in ]
# (so, this includes emacs ~-backups, CVS detritus, etc.)
#
# It ignores any directory matching $excluded_directories
# (so, you should add here any sources imported but not covered under
# the license.)
#

my $excluded_directories = '^(CVS|generated)$';
my $excluded_paths = '^(';
# note: first excluded path regexp must not start with a '|'
# different license
$excluded_paths .= 'cmake/CodeCoverage.cmake';
$excluded_paths .= '|cmake/FindCython.cmake';
$excluded_paths .= '|cmake/FindPythonExtensions.cmake';
$excluded_paths .= '|cmake/UseCython.cmake';
$excluded_paths .= '|cmake/targetLinkLibrariesWithDynamicLookup.cmake';
$excluded_paths .= '|cmake/version-base.cmake';
# minisat license
$excluded_paths .= '|src/prop/(bv)?minisat/core/.*';
$excluded_paths .= '|src/prop/(bv)?minisat/mtl/.*';
$excluded_paths .= '|src/prop/(bv)?minisat/simp/.*';
$excluded_paths .= '|src/prop/(bv)?minisat/utils/.*';
$excluded_paths .= ')$';

# Years of copyright for the template.  E.g., the string
# "1985, 1987, 1992, 1997, 2008" or "2006-2009" or whatever.
my $years = '2009-2023';

my $standard_template = <<EOF;
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) $years by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
EOF

my $doc_template = <<EOF;
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \\todo document this file
 */
EOF

my $standard_template_hash = $standard_template;
$standard_template_hash =~ s/ \* \*/\# \#\#/g;
$standard_template_hash =~ s/ \*/\#/g;
$standard_template_hash =~ s/\*/\#/g;
my $doc_template_hash = $doc_template;
$doc_template_hash =~ s/ \*/\#/g;
$doc_template_hash =~ s/\#\//\#\#/g;


## end config ##

use strict;
use Fcntl ':mode';

my $dir = $0;
$dir =~ s,/[^/]+/*$,,;

if($#ARGV >= 0 && ($ARGV[0] eq '-h' || $ARGV[0] eq '--help')) {
  open(my $SELF, $0) || die "error opening $0 for reading";
  while($_ = <$SELF>) {
    last if !/^#/;
    print;
  }
  close $SELF;
  exit;
}

# whether we ONLY process files with git status "M"
my $modonly = 0;

if($#ARGV >= 0 && $ARGV[0] eq '-m') {
  $modonly = 1;
  shift;
}

my @searchdirs = ();
if($#ARGV == -1) {
  (chdir($dir."/..") && -f "src/include/cvc5_public.h") || die "can't find top-level source directory for cvc5";
  my $pwd = `pwd`; chomp $pwd;

  print <<EOF;
Warning: this script is dangerous.  It will overwrite the header comments in your
source files to match the template in the script, attempting to retain file-specific
comments, but this isn't guaranteed.  You should run this in a git working tree
and run "git diff" after to ensure everything was correctly rewritten.

The directories in which to search for and change sources is:
  $pwd/CMakeLists.txt
  $pwd/cmake
  $pwd/src
  $pwd/examples
  $pwd/test
  $pwd/doc
  $pwd/docs

Continue? y or n:
EOF

  $_ = <STDIN>; chomp;
  die 'aborting operation' if !( $_ eq 'y' || $_ eq 'yes' || $_ eq 'Y' || $_ eq 'YES' );

  $searchdirs[0] = 'CMakeLists.txt';
  $searchdirs[1] = 'cmake';
  $searchdirs[2] = 'src';
  $searchdirs[3] = 'examples';
  $searchdirs[4] = 'test';
} else {
  @searchdirs = @ARGV;
}

print "Updating sources...\n";

while($#searchdirs >= 0) {
  my $dir = shift @searchdirs;
  $dir =~ s,\/$,,;              # remove trailing slash from directory
  my $mode = (stat($dir))[2] || warn "file or directory \`$dir' does not exist!";
  my $is_directory = S_ISDIR($mode);
  if ($is_directory) {
    recurse($dir);
  } else {
    if ($dir =~ m,^(.*)\/([^/]*)$,) {
      my ($dir, $file) = ($1, $2);
      if ($dir eq "") {
        $dir = "/";
      }
      handleFile($dir, $file);
    } else {
      handleFile(".", $dir);
    }
  }
}

sub reqHashPrefix {
  my ($file) = @_;
  return ($file =~ /\.(cmake|py)(\.in)?$/ or $file =~ /CMakeLists\.txt/);
}

sub printHeader {
  my ($OUT, $file) = @_;
  if (reqHashPrefix($file)) {
    print $OUT "###############################################################################\n";
  } elsif ($file =~ /\.g$/) {
    # avoid javadoc-style comment here; antlr complains
    print $OUT "/* ****************************************************************************\n"
  } else {
    print $OUT "/******************************************************************************\n"
  }
}

sub printTopContrib {
  my ($OUT, $file, $authors) = @_;
  my $comment_style = " *";
  if (reqHashPrefix($file)) {
    $comment_style = "#";
  }
  print $OUT "$comment_style Top contributors (to current version):\n";
  print $OUT "$comment_style   $authors\n";
}

sub handleFile {
  my ($srcdir, $file) = @_;
  return if !($file =~ /\.(c|cc|cpp|h|hh|hpp|g|java)(\.in)?$/ or reqHashPrefix($file));
  return if ($srcdir.'/'.$file) =~ /$excluded_paths/;
  return if $modonly && `git status -s "$srcdir/$file" 2>/dev/null` !~ /^(M|.M)/;
  print "$srcdir/$file... ";
  my $infile = $srcdir.'/'.$file;
  my $outfile = $srcdir.'/#'.$file.'.tmp';
  open(my $IN, $infile) || die "error opening $infile for reading";
  open(my $OUT, '>', $outfile) || die "error opening $outfile for writing";
  open(my $AUTHOR, "$dir/get-authors " . $infile . '|');
  my $authors = <$AUTHOR>; chomp $authors;
  close $AUTHOR;

  # Read file into array
  my @lines = <$IN>;
  close $IN;

  # Check if file contains a shebang and print it as first line.
  if ($lines[0] =~ /^\#!/) {
    print $OUT $lines[0];
    shift @lines;
  }

  printHeader($OUT, $file);
  printTopContrib($OUT, $file, $authors);

  my $adding = 0;
  # Copyright header already exists
  if ($lines[0] =~ /^(%\{)?\/\*{78}/
      or $lines[0] =~ /^(%\{)?\/\* \*{76}/
      or $lines[0] =~ /^\#{79}$/) {
    print "updating\n";

    # Skip lines until copyright header end and preserve copyright of non cvc5
    # authors.
    my $found_header_end = 0;
    while (my $line = shift @lines) {
      # Check if someone else holds this copyright and keep it.
      if($line =~ /\b[Cc]opyright\b/ && $line !~ /\bby the authors listed in the file AUTHORS\b/) {
        print $OUT $line;
      }
      # Reached end of copyright header section
      if ($line =~ /^ \* \*{76}\s*$/ or $line =~ /^\# \#{77}$/) {
        $found_header_end = 1;
        last;
      }
    }
    if (!$found_header_end) {
      die "error: did not find end of copyright header secion for file '$file'";
    }
  # No header found
  } else {
    print "adding\n";
    $adding = 1;
  }
  if (reqHashPrefix($file)) {
    print $OUT $standard_template_hash;
    if ($adding) {
      print $OUT $doc_template_hash;
    }
  } else {
    print $OUT $standard_template;
    if ($adding) {
      print $OUT $doc_template;
    }
  }
  # Print remaining file
  foreach (@lines) {
    print $OUT $_;
  }
  close $OUT;

  # Preserve file permissions of $infile
  my $perm = (stat($infile))[2] & 0777;
  chmod $perm, $outfile;

  rename($outfile, $infile) || die "can't rename working file \`$outfile' to \`$infile'";
}

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
      handleFile($srcdir, $file);
    }
  }
  closedir $DIR;
}

### Local Variables:
### perl-indent-level: 2
### End:
