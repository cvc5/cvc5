#!/usr/bin/perl -w
# DIMACS to SMT
# Morgan Deters
# Copyright (c) 2009, 2010, 2011  The CVC4 Project

use strict;

my ($nvars, $nclauses);
while(<>) {
    next if /^c/;

    if(/^p cnf (\d+) (\d+)/) {
        ($nvars, $nclauses) = ($1, $2);
        print "(benchmark b\n";
        print ":status unknown\n";
        print ":logic QF_UF\n";
        for(my $i = 1; $i <= $nvars; ++$i) {
            print ":extrapreds ((x$i))\n";
        }
        print ":formula (and\n";
        next;
    }

    print "(or";
    chomp;
    @_ = split(/ /);
    for(my $i = 0; $i < $#_; ++$i) {
        if($_[$i] < 0) {
            print " (not x" . -$_[$i] . ")";
        } else {
            print " x" . $_[$i];
        }
    }
    print ")\n";
}

print "))\n";
