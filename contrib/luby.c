// luby.c - Luby sequence generator
// Morgan Deters <mdeters@cs.nyu.edu> for the CVC4 project, 5 May 2011
//
// This program enumerates the Luby-based MiniSat 2 restart sequence.
// MiniSat restarts after a number of conflicts determined by:
//
//    restart_base * luby(restart_inc, curr_restarts)
//
// By default, MiniSat has restart_base = 25, restart_inc = 3.0, and
// curr_restarts is the number of restarts that have been done (so it
// starts at 0).
//
// For the Luby paper, see:
//   http://citeseer.ist.psu.edu/viewdoc/summary?doi=10.1.1.47.5558
//
// Compile luby.c with gcc -o luby luby.c -lm
//

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>

// luby() function copied from MiniSat 2
// Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
// Copyright (c) 2007-2010, Niklas Sorensson
double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

int main(int argc, char *argv[]) {
  int N;
  int base;
  double inc;
  int i;

  if(argc != 4) {
    fprintf(stderr, "usage: %s base inc N\n"
            "In MiniSat 2, base==25 and inc==3 by default.\n"
            "base is simply a multiplier after the sequence is computed.\n"
            "N is the number to produce (-1 means run until CTRL-C)\n",
            argv[0]);
    exit(1);
  }

  base = atoi(argv[1]);
  inc = strtod(argv[2], NULL);
  N = atoi(argv[3]);

  assert(base >= 1);
  assert(inc >= 1.0);

  for(i = 0; N < 0 || i < N; ++i) {
    printf("%d %f\n", i, luby(inc, i) * base);
  }
}
