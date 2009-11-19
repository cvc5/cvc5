#include <string>
#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <string.h>
#include <signal.h>

#include "util/exception.h"
#include "config.h"

using CVC4::Exception;
using namespace std;

namespace CVC4 {
namespace Main {

void sigint_handler(int sig, siginfo_t* info, void*) {
  fprintf(stderr, "CVC4 interrupted by user.\n");
  abort();
}

void segv_handler(int sig, siginfo_t* info, void*) {
  fprintf(stderr, "CVC4 suffered a segfault.\n");
  abort();
}

void cvc4_init() throw() {
  struct sigaction act1;
  act1.sa_sigaction = sigint_handler;
  act1.sa_flags = SA_SIGINFO;
  sigemptyset(&act1.sa_mask);
  if(sigaction(SIGINT, &act1, NULL))
    throw new Exception(string("sigaction(SIGINT) failure: ") + strerror(errno));

  struct sigaction act2;
  act2.sa_sigaction = segv_handler;
  act2.sa_flags = SA_SIGINFO;
  sigemptyset(&act2.sa_mask);
  if(sigaction(SIGSEGV, &act2, NULL))
    throw new Exception(string("sigaction(SIGSEGV) failure: ") + strerror(errno));
}

}/* CVC4::Main namespace */
}/* CVC4 namespace */
