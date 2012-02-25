#include <signal.h>
#include <stdlib.h>
#include <string.h>

#include "picosat.h"

int picosat_main (int, char **);

static int catched;

static void (*sig_int_handler);
static void (*sig_segv_handler);
static void (*sig_abrt_handler);
static void (*sig_term_handler);
#ifndef NALLSIGNALS
static void (*sig_kill_handler);
static void (*sig_xcpu_handler);
static void (*sig_xfsz_handler);
#endif

static void
resetsighandlers (void)
{
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
#ifndef NALLSIGNALS
  (void) signal (SIGKILL, sig_kill_handler);
  (void) signal (SIGXCPU, sig_xcpu_handler);
  (void) signal (SIGXFSZ, sig_xfsz_handler);
#endif
}

static void
message (int sig)
{
  picosat_message (1, "");
  picosat_message (1, "*** CAUGHT SIGNAL %d ***", sig);
  picosat_message (1, "");
}

static void
catch (int sig)
{
  if (!catched)
    {
      message (sig);
      catched = 1;
      picosat_stats ();
      message (sig);
    }

  resetsighandlers ();
  raise (sig);
}

static void
setsighandlers (void)
{
  sig_int_handler = signal (SIGINT, catch);
  sig_segv_handler = signal (SIGSEGV, catch);
  sig_abrt_handler = signal (SIGABRT, catch);
  sig_term_handler = signal (SIGTERM, catch);
#ifndef NALLSIGNALS
  sig_kill_handler = signal (SIGKILL, catch);
  sig_xcpu_handler = signal (SIGXCPU, catch);
  sig_xfsz_handler = signal (SIGXFSZ, catch);
#endif
}

int
main (int argc, char **argv)
{
  int res, verbose;

  for (verbose = argc - 1; verbose; verbose--)
    if (!strcmp (argv[verbose], "-v"))
      break;

  if (verbose)
    setsighandlers ();

  res = picosat_main (argc, argv);

  if (verbose)
    resetsighandlers ();

  return res;
}
