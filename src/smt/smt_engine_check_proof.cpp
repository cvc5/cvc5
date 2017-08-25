/*********************                                                        */
/*! \file smt_engine_check_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Guy Katz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__MINGW64__)
#include <io.h>
#endif
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <string>

#include "base/configuration_private.h"
#include "base/cvc4_assert.h"
#include "base/output.h"
#include "smt/smt_engine.h"
#include "util/statistics_registry.h"

#if (IS_LFSC_BUILD && IS_PROOFS_BUILD)
#include "lfscc.h"
#endif

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

#if (IS_LFSC_BUILD && IS_PROOFS_BUILD)

  Chat() << "generating proof..." << endl;

  Proof* pf = getProof();

  Chat() << "checking proof..." << endl;

  std::string logicString = d_logic.getLogicString();

  if (!(
        // Pure logics
        logicString == "QF_UF" ||
        logicString == "QF_AX" ||
        logicString == "QF_BV" ||
        // Non-pure logics
        logicString == "QF_AUF" ||
        logicString == "QF_UFBV" ||
        logicString == "QF_ABV" ||
        logicString == "QF_AUFBV"
        )) {
    // This logic is not yet supported
    Notice() << "Notice: no proof-checking for " << logicString << " proofs yet" << endl;
    return;
  }

  char *pfFile = tempnam(NULL, "cvc4_");
  if (!pfFile) {
    Notice() << "Error: couldn't get path from tempnam() during proof checking" << endl;
    return;
  }
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__MINGW64__)
  int fd = _open(pfFile,
                 _O_CREAT | _O_EXCL | _O_SHORT_LIVED | _O_RDWR,
                 _S_IREAD | _S_IWRITE);
#else
  mode_t openmode = S_IRUSR | S_IWUSR;
  int fd = open(pfFile, O_CREAT | O_EXCL | O_RDWR, openmode);
#endif
  if (fd == -1) {
    free(pfFile);
    Notice() << "Error: failed to open temporary file during proof checking" << endl;
    return;
  }

  // ensure this temp file is removed after
  smt::UnlinkProofFile unlinker(pfFile);

  ofstream pfStream(pfFile);
  pfStream << proof::plf_signatures << endl;
  pf->toStream(pfStream);
  pfStream.close();
  lfscc_init();
  lfscc_check_file(pfFile, false, false, false, false, false, false, false);
  // FIXME: we should actually call lfscc_cleanup here, but lfscc_cleanup
  // segfaults on regress0/bv/core/bitvec7.smt
  //lfscc_cleanup();
  free(pfFile);
  close(fd);

#else /* (IS_LFSC_BUILD && IS_PROOFS_BUILD) */
  Unreachable("This version of CVC4 was built without proof support; cannot check proofs.");
#endif /* (IS_LFSC_BUILD && IS_PROOFS_BUILD) */
}
