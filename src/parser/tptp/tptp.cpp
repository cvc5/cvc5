/*********************                                                        */
/*! \file tptp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Francois Bobot, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of TPTP constants.
 **
 ** Definitions of TPTP constants.
 **/

// Do not #include "parser/antlr_input.h" directly. Rely on the header.
#include "parser/tptp/tptp.h"

#include "expr/type.h"
#include "parser/parser.h"

// ANTLR defines these, which is really bad!
#undef true
#undef false

namespace CVC4 {
namespace parser {

Tptp::Tptp(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  Parser(exprManager,input,strictMode,parseOnly) {
  addTheory(Tptp::THEORY_CORE);

  /* Try to find TPTP dir */
  // From tptp4x FileUtilities
  //----Try the TPTP directory, and TPTP variations
  char* home = getenv("TPTP");
  if(home == NULL) {
     home = getenv("TPTP_HOME");
// //----If no TPTP_HOME, try the tptp user (aaargh)
//         if(home == NULL && (PasswdEntry = getpwnam("tptp")) != NULL) {
//            home = PasswdEntry->pw_dir;
//         }
//----Now look in the TPTP directory from there
    if(home != NULL) {
      d_tptpDir = home;
      d_tptpDir.append("/TPTP/");
    }
  } else {
    d_tptpDir = home;
    //add trailing "/"
    if(d_tptpDir[d_tptpDir.size() - 1] != '/') {
      d_tptpDir.append("/");
    }
  }
  d_hasConjecture = false;
}

Tptp::~Tptp() {
  for( unsigned i=0; i<d_in_created.size(); i++ ){
    d_in_created[i]->free(d_in_created[i]);
  }
}

void Tptp::addTheory(Theory theory) {
  ExprManager * em = getExprManager();
  switch(theory) {
  case THEORY_CORE:
    //TPTP (CNF and FOF) is unsorted so we define this common type
    {
      std::string d_unsorted_name = "$$unsorted";
      d_unsorted = em->mkSort(d_unsorted_name);
      preemptCommand( new DeclareTypeCommand(d_unsorted_name, 0, d_unsorted) );
    }
    // propositionnal
    defineType("Bool", em->booleanType());
    defineVar("$true", em->mkConst(true));
    defineVar("$false", em->mkConst(false));
    addOperator(kind::AND);
    addOperator(kind::EQUAL);
    addOperator(kind::IMPLIES);
    //addOperator(kind::ITE); //only for tff thf
    addOperator(kind::NOT);
    addOperator(kind::OR);
    addOperator(kind::XOR);
    addOperator(kind::APPLY_UF);
    //Add quantifiers?
    break;

  default:
    std::stringstream ss;
    ss << "internal error: Tptp::addTheory(): unhandled theory " << theory;
    throw ParserException(ss.str());
  }
}


/* The include are managed in the lexer but called in the parser */
// Inspired by http://www.antlr3.org/api/C/interop.html

bool newInputStream(std::string fileName, pANTLR3_LEXER lexer, std::vector< pANTLR3_INPUT_STREAM >& inc ) {
  Debug("parser") << "Including " << fileName << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM    in;
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8) fileName.c_str());
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8) fileName.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  if(in == NULL) {
    Debug("parser") << "Can't open " << fileName << std::endl;
    return false;
  }
  // Same thing as the predefined PUSHSTREAM(in);
  lexer->pushCharStream(lexer,in);
  // restart it
  //lexer->rec->state->tokenStartCharIndex	= -10;
  //lexer->emit(lexer);

  // Note that the input stream is not closed when it EOFs, I don't bother
  // to do it here, but it is up to you to track streams created like this
  // and destroy them when the whole parse session is complete. Remember that you
  // don't want to do this until all tokens have been manipulated all the way through
  // your tree parsers etc as the token does not store the text it just refers
  // back to the input stream and trying to get the text for it will abort if you
  // close the input stream too early.
  //
  inc.push_back( in );

  //TODO what said before
  return true;
}

/* overridden popCharStream for the lexer - necessary if we had symbol
 * filtering in file inclusion.
void Tptp::myPopCharStream(pANTLR3_LEXER lexer) {
  ((Tptp*)lexer->super)->d_oldPopCharStream(lexer);
  ((Tptp*)lexer->super)->popScope();
}
*/

void Tptp::includeFile(std::string fileName) {
  // security for online version
  if(!canIncludeFile()) {
    parseError("include-file feature was disabled for this run.");
  }

  // Get the lexer
  AntlrInput * ai = static_cast<AntlrInput *>(getInput());
  pANTLR3_LEXER lexer = ai->getAntlr3Lexer();

  // set up popCharStream - would be necessary for handling symbol
  // filtering in inclusions
  /*
  if(d_oldPopCharStream == NULL) {
    d_oldPopCharStream = lexer->popCharStream;
    lexer->popCharStream = myPopCharStream;
  }
  */

  // push the inclusion scope; will be popped by our special popCharStream
  // would be necessary for handling symbol filtering in inclusions
  //pushScope();

  // get the name of the current stream "Does it work inside an include?"
  const std::string inputName = ai->getInputStreamName();

  // Test in the directory of the actual parsed file
  std::string currentDirFileName;
  if(inputName != "<stdin>") {
    // TODO: Use dirname or Boost::filesystem?
    size_t pos = inputName.rfind('/');
    if(pos != std::string::npos) {
      currentDirFileName = std::string(inputName, 0, pos + 1);
    }
    currentDirFileName.append(fileName);
    if(newInputStream(currentDirFileName,lexer, d_in_created)) {
      return;
    }
  } else {
    currentDirFileName = "<unknown current directory for stdin>";
  }

  if(d_tptpDir.empty()) {
    parseError("Couldn't open included file: " + fileName
               + " at " + currentDirFileName + " and the TPTP directory is not specified (environment variable TPTP)");
  };

  std::string tptpDirFileName = d_tptpDir + fileName;
  if(! newInputStream(tptpDirFileName,lexer, d_in_created)) {
    parseError("Couldn't open included file: " + fileName
               + " at " + currentDirFileName + " or " + tptpDirFileName);
  }
}

void Tptp::checkLetBinding(std::vector<Expr>& bvlist, Expr lhs, Expr rhs, bool formula) {
  if(lhs.getKind() != CVC4::kind::APPLY_UF) {
    parseError("malformed let: LHS must be a flat function application");
  }
  std::vector<CVC4::Expr> v = lhs.getChildren();
  if(formula && !lhs.getType().isBoolean()) {
    parseError("malformed let: LHS must be formula");
  }
  for(size_t i = 0; i < v.size(); ++i) {
    if(v[i].hasOperator()) {
      parseError("malformed let: LHS must be flat, illegal child: " + v[i].toString());
    }
  }
  std::sort(v.begin(), v.end());
  std::sort(bvlist.begin(), bvlist.end());
  // ensure all let-bound variables appear on the LHS, and appear only once
  for(size_t i = 0; i < bvlist.size(); ++i) {
    std::vector<CVC4::Expr>::const_iterator found = std::lower_bound(v.begin(), v.end(), bvlist[i]);
    if(found == v.end() || *found != bvlist[i]) {
      parseError("malformed let: LHS must make use of all quantified variables, missing `" + bvlist[i].toString() + "'");
    }
    std::vector<CVC4::Expr>::const_iterator found2 = found + 1;
    if(found2 != v.end() && *found2 == *found) {
      parseError("malformed let: LHS cannot use same bound variable twice: " + (*found).toString());
    }
  }
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
