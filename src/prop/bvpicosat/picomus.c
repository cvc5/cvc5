/****************************************************************************
Copyright (c) 2010, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
****************************************************************************/

#include "picosat.h"

#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>

#define MAXNONREDROUNDS 3
#define MINCOREROUNDS 5
#define MAXCOREROUNDS 100

typedef struct Cls { int lit, red, * lits; } Cls;

static int verbose;
static int fclose_input, pclose_input, close_output;
static FILE * input_file, * output_file;
static const char * input_name, * output_name;
static int lineno = 1;
static int nvars, nclauses;
static Cls * clauses;
static int * lits, nlits, szlits;
static double start;
static int reductions;

static int next (void) {
  int res = fgetc (input_file);
  if (res == '\n') lineno++;
  return res;
}

static void msg (const char * fmt, ...) {
  va_list ap;
  if (!verbose) return;
  fputs ("c [picomus] ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static const char * parse (void) {
  int ch, n, lit, sign, i;
  Cls * c;
HEADER:
  ch = next ();
  if (ch == 'c') {
    while ((ch = next ()) != '\n')
      if (ch == EOF) return "EOF after 'c'";
    goto HEADER;
  }
  if (ch == '\r') goto HEADER;
  if (ch != 'p') return "expected 'c' or 'p'";
  if (fscanf (input_file, " cnf %d %d", &nvars, &nclauses) != 2)
    return "invalid header";
  msg ("p cnf %d %d", nvars, nclauses);
  clauses = calloc (nclauses, sizeof *clauses);
  lit = n = 0;
LIT:
  ch = next ();
  if (ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r') goto LIT;
  if (ch == 'c') {
    while ((ch = next ()) != '\n')
      if (ch == EOF) return "EOF after 'c'";
    goto LIT;
  }
  if (ch == EOF) {
    if (lit) return "zero missing";
    if (n < nclauses) return "clauses missing";
    return 0;
  }
  if (n == nclauses) return "too many clauses";
  if (ch == '-') {
    sign = -1;
    ch = next ();
    if (!isdigit (ch)) return "expected digit after '-'";
  } else sign = 1;
  if (!isdigit (ch)) return "expected digit";
  lit = ch - '0';
  while (isdigit (ch = next ()))
    lit = 10 * lit + (ch - '0');
  if (lit > nvars) return "maximum variable index exceeded";
  if (lit) {
    lit *= sign;
    if (nlits == szlits) {
      szlits = szlits ? 2 * szlits : 1;
      lits = realloc (lits, szlits * sizeof *lits);
    }
    lits[nlits++] = lit;
  } else {
    c = clauses + n++;
    c->lits = malloc ((nlits + 1) * sizeof *c->lits);
    for (i = 0; i < nlits; i++)
      c->lits[i] = lits[i];
    c->lits[i] = 0;
    nlits = 0;
  }
  goto LIT;
}

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** picomus: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static double percent (double a, double b) { return b?100.0*a/b:0.0; }

static void callback (void * dummy, const int * mus) {
  int remaining;
  const int * p;
  (void) dummy;
  if (!verbose) return;
  remaining = 0;
  for (p = mus; *p; p++) remaining++;
  assert (remaining <= nclauses);
  reductions++;
  msg ("reduction %d to %d out of %d (%.0f%%) after %.1f sec",
       reductions,
       remaining, nclauses, percent (remaining, nclauses),
       picosat_time_stamp () - start);
}

int main (int argc, char ** argv) {
  int i, * p, n, oldn, red, nonred, tmp, res, round, printed, len;
  const char * err;
  const int * q;
  char * cmd;
  Cls * c;
  start = picosat_time_stamp ();
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) {
      printf (
        "picomus [-v][-h][<input>[<output>]]\n"
        "\n"
	"This tool is a SAT solver that uses the PicoSAT library to\n"
	"generate a 'minimal unsatisfiable core' also known as 'minimal\n"
	"unsatisfiable set' (MUS) of a CNF in DIMACS format.\n"
        "\n"
        "Both file argumetns can be \"-\" and then denote <stdin> resp.\n"
        "<stdout>.  If no input file is given <stdin> is used.  If no\n"
	"output file is specified the MUS is only computed, but not\n"
	"printed.\n"
	"\n"
	"Otherwise the output conforms to the standard SAT solver\n"
	"format used at SAT competitions.\n"
	"\n"
#ifndef TRACE
	"WARNING: PicosSAT is compiled without trace support.\n"
	"\n"
	"This typically slows down this MUS extractor, since\n"
	"it only relies on clause selector variables and\n"
	"can not make use of core extraction.  To enable\n"
	"trace generation use './configure --trace' or\n"
	"'./configure -O --trace' when building PicoSAT.\n"
#else
	"Since trace generation code is included, this binary\n"
	"uses both core extraction and clause selector variables.\n"
#endif
	);
      exit (0);
    } else if (!strcmp (argv[i], "-v")) verbose++;
    else if (output_name) die ("too many arguments");
    else if (!input_name) input_name = argv[i];
    else output_name = argv[i];
  }
  if (input_name && strcmp (input_name, "-")) {
    len = strlen (input_name);
    if (len >= 3 && !strcmp (input_name + len - 3, ".gz")) {
      cmd = malloc (len + 20);
      sprintf (cmd, "gunzip -c %s 2>/dev/null", input_name);
      input_file = popen (cmd, "r");
      pclose_input = 1;
      free (cmd);
    } else input_file = fopen (input_name, "r"), fclose_input = 1;
    if (!input_file) die ("can not read '%s'", input_name);
  } else input_file = stdin, input_name = "-";
  if ((err =  parse ())) {
    fprintf (stderr, "%s:%d: %s\n", input_name, lineno, err);
    fflush (stderr);
    exit (1);
  }
  if (fclose_input) fclose (input_file);
  if (pclose_input) pclose (input_file);
  picosat_init ();
  picosat_set_prefix ("c [picosat] ");
  picosat_set_output (stderr);
  if (verbose > 1) picosat_set_verbosity (verbose - 1);
  printed = 0;
  if (picosat_enable_trace_generation ()) {
    n = nclauses;
    nonred = 0;
    for (round = 1; round <= MAXCOREROUNDS; round++) {
      if (verbose > 1)
	msg ("starting core extraction round %d", round);
      picosat_set_seed (round);
      for (i = 0; i < nclauses; i++) {
	c = clauses + i;
	if (c->red) {
	  picosat_add (1);
	  picosat_add (-1);
	} else {
	  for (p = c->lits; *p; p++)
	    picosat_add (*p);
	}
	tmp = picosat_add (0);
	assert (tmp == i);
      }
      res = picosat_sat (-1);
      if (res == 10) { assert (round == 1); goto SAT; }
      assert (res == 20);
      if (!printed) {
	assert (round == 1);
	printed = 1;
	printf ("s UNSATISFIABLE\n");
	fflush (stdout);
      }
      for (i = 0; i < nclauses; i++) {
	c = clauses + i;
	if (c->red) { assert (!picosat_coreclause (i)); continue; }
	if (picosat_coreclause (i)) continue;
	c->red = 1;
      }
      oldn = n;
      n = 0;
      for (i = 0; i < nclauses; i++) if (!clauses[i].red) n++;
      msg ("extracted core %d of size %d out of %d (%.0f%%) after %.1f sec",
	   round, n, nclauses, percent (n, nclauses),
	   picosat_time_stamp () - start);
      assert (oldn >= n);
      picosat_reset ();
      picosat_init ();
      picosat_set_prefix ("c [picosat] ");
      picosat_set_output (stderr);
      if (round >= MINCOREROUNDS) {
	red = oldn - n;
	if (red < 10 && (100*red + 99)/oldn < 2) {
	  nonred++;
	  if (nonred > MAXNONREDROUNDS) break;
	}
      }
      if (round < MAXCOREROUNDS) picosat_enable_trace_generation ();
    }
  }
  for (i = 0; i < nclauses; i++) {
    c = clauses + i;
    if (c->red) {
      picosat_add (1);
      picosat_add (-1);
      tmp = picosat_add (0);
      assert (tmp == i);
      continue;
    }
    c->lit = nvars + i + 1;
    picosat_add (-c->lit);
    for (p = c->lits; *p; p++)
      (void) picosat_add (*p);
    tmp = picosat_add (0);
    assert (tmp == i);
  }
  for (i = 0; i < nclauses; i++) {
    c = clauses + i;
    if (c->red) continue;
    picosat_assume (c->lit);
  }
  res = picosat_sat (-1);
  if (res == 20) {
    if (!printed) printf ("s UNSATISFIABLE\n"), fflush (stdout);
    for (i = 0; i < nclauses; i++) clauses[i].red = 1;
    q = picosat_mus_assumptions (0, callback, 1);
    while ((i = *q++)) {
      i -= nvars + 1;
      assert (0 <= i && i < nclauses);
      clauses[i].red = 0;
    }
  } else {
SAT:
    assert (res == 10);
    printf ("s SATISFIABLE\n"); fflush (stdout);
    for (i = 1; i <= nvars; i++)
      printf ("v %d\n", ((picosat_deref (i) < 0) ? -1 : 1) * i);
    printf ("v 0\n");
  }
  if (verbose) picosat_stats ();
  picosat_reset ();
  n = 0;
  for (i = 0; i < nclauses; i++) if (!clauses[i].red) n++;
  red = nclauses - n;
  msg ("found %d redundant clauses %.0f%%", red, percent (red, nclauses));
  if (output_name && strcmp (output_name, "-")) {
    output_file = fopen (output_name, "w");
    if (!output_file) die ("can not write '%s'", output_name);
    close_output = 1;
  } else if (output_name && !strcmp (output_name, "-")) output_file = stdout;
  if (output_file) {
    fprintf (output_file, "p cnf %d %d\n", nvars, n);
    for (i = 0; i < nclauses; i++) 
      if (!clauses[i].red) {
	for (p = clauses[i].lits; *p; p++) fprintf (output_file, "%d ", *p);
	fprintf (output_file, "0\n");
      }
    if (close_output) fclose (output_file);
  }
  msg ("%s %d irredundant clauses %.0f%%",
       output_file ? "printed" : "computed", n, percent (n, nclauses));
  for (i = 0; i < nclauses; i++) free (clauses[i].lits);
  free (clauses);
  free (lits);
  msg ("%d reductions in %.1f seconds", 
       reductions, picosat_time_stamp () - start);
  return res;
}
