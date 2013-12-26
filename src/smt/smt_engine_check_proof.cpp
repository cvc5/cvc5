/*********************                                                        */
/*! \file smt_engine_check_proof.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "smt/smt_engine.h"
#include "util/statistics_registry.h"
#include "check.h"

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <string>
#include <unistd.h>

using namespace CVC4;
using namespace std;

namespace CVC4 {

namespace proof {
  extern const char *const plf_signatures;
}/* CVC4::proof namespace */

namespace smt {

class UnlinkProofFile {
  string d_filename;
public:
  UnlinkProofFile(const char* filename) : d_filename(filename) {}
  ~UnlinkProofFile() { unlink(d_filename.c_str()); }
};/* class UnlinkProofFile */

}/* CVC4::smt namespace */

}/* CVC4 namespace */

void SmtEngine::checkProof() {

#ifdef CVC4_PROOF

  Chat() << "generating proof..." << endl;

  Proof* pf = getProof();

  Chat() << "checking proof..." << endl;

  if(!d_logic.isPure(theory::THEORY_BOOL) &&
     !d_logic.isPure(theory::THEORY_UF)) {
    // no checking for these yet
    Notice() << "Notice: no proof-checking for non-UF proofs yet" << endl;
    return;
  }

  char* pfFile = strdup("/tmp/cvc4_proof.XXXXXX");
  int fd = mkstemp(pfFile);

  // ensure this temp file is removed after
  smt::UnlinkProofFile unlinker(pfFile);

  ofstream pfStream(pfFile);
  pfStream << proof::plf_signatures << endl;
  pf->toStream(pfStream);
  pfStream.close();
  args a;
  a.show_runs = false;
  a.no_tail_calls = false;
  a.compile_scc = false;
  a.compile_scc_debug = false;
  a.run_scc = false;
  a.use_nested_app = false;
  a.compile_lib = false;
  init();
  check_file(pfFile, args());
  close(fd);

#else /* CVC4_PROOF */

  Unreachable("This version of CVC4 was built without proof support; cannot check proofs.");

#endif /* CVC4_PROOF */

}
